###############################################################################
#  IrreducibilityLeanProofWriter.sage
#
#  Updated version of the irreducibility script of the predecessor project
#  (github.com/alainchmt/RingOfIntegersProject):
#      IrreducibilityLeanProofWriter.sage
#
#  Given a polynomial T in ZZ[x] it writes one Lean file holding an
#  irreducibility certificate for T, ending in `theorem irreducible_T`.
#  Three certificate shapes are emitted, as in the original: a pure
#  factorisation certificate when the prime reductions already force the
#  degree, otherwise one of the two (LPFW) certificates.
#
#  Entry point:
#      write_irreducible_lean(T, out_file=..., native=False)
#
#  Usage:
#      load('IrreducibilityLeanProofWriter.sage')
#      R.<x> = PolynomialRing(ZZ)
#      write_irreducible_lean(x^8 - x^6 + 2*x^4 + x^2 + 1, 'Irreducible8.lean')
#
#  Updated with the help of Claude Code (Opus 5).
###############################################################################

from itertools import combinations
import itertools
import os
import re


KERNEL_FIELDS = ['honed', 'hc_le', 'hsub', 'hindab', 'hinter', 'hmulw',
                 'hprod', 'hmul1', 'hmul2', 'hvFrobKer', 'hwFrobComp',
                 'hrhoeq', 'hrho']

_FIELD_DECIDE = re.compile(r'(?m)^(\s*[A-Za-z_][A-Za-z0-9_]*\s*:=\s*by )decide([ \t]*)$')

_LINEAR_DECIDE = re.compile(r'(irreducible_ofList_of_linear[^\n]*?)\(by decide\)')


def _retactic(text, native=False):
    """Rewrite the emitted tactics.

    The certificate emitters below all emit `by decide`; rather than thread a
    selector through every one of them, the choice is applied here.  That keeps
    them diffable against their source.
    """
    if native:
        text = _FIELD_DECIDE.sub(r'\1native_decide\2', text)
        text = _LINEAR_DECIDE.sub(r'\1(by native_decide)', text)
    else:
        for fld in KERNEL_FIELDS:
            text = re.sub(r'(?m)^(\s*%s\s*:=\s*by )decide([ \t]*)$' % re.escape(fld),
                          r'\1decide +kernel\2', text)
    # No `unseal` is needed once the rational fields go through the kernel.
    text = re.sub(r'(?m)^unseal Rat\.add Rat\.mul Rat\.inv\n', '', text)
    return text

def sqpow(t, f, p):
    s = p.bit_length() - 1
    binary_list = [int(bit) for bit in bin(p)[2:]]
    bit = binary_list[::-1]
    hp = [0 for i in range(s)] + [t]
    gp = [0 for i in range(s)]
    for i in range(s-1, -1, -1):
        gp[i], hp[i] = (hp[i+1] ^ 2 * t^(bit[i])).quo_rem(f)
    return hp, gp


def factorLists(T, p):
    F = factor(T.change_ring(GF(p)))
    Fp = [x for x in F]
    Fp[0] = (F.unit() * F[0][0], F[0][1])
    lF = []
    for p in Fp:
        lF = lF + p[1] * [p[0].list()]
    return lF


def ListDegree(T, p):
    deg = T.degree()
    d = []
    for P in factor(T.change_ring(GF(p))):
        d = d + P[1] * [P[0].degree()]
    return d


def SubSums(l):
    sub = [0]
    for i in range(1, len(l) + 1):
        combs = [list(x) for x in combinations(l, i)]
        if len(combs) > 0:
            aux = [sum(c) for c in combs]
            sub = sub + aux
    return sub


def IntersectListDegrees(T, l):
    inter = SubSums(ListDegree(T, l[0]))
    for p in l:
        inter = set(inter).intersection(set(SubSums(ListDegree(T, p))))
    return inter


def FindMinimalCommonDegree(T, size, rangep):
    C = []
    dmin = 1
    GPrimes = [p for p in primes(rangep) if T.leading_coefficient() % p != 0]
    for l in [list(x) for x in combinations(GPrimes, size)]:
        if min((IntersectListDegrees(T, l)) - {0}) >= dmin:
            dmin = min((IntersectListDegrees(T, l)) - {0})
            C = C + [(dmin, l)]
    Cp = []
    for x in C:
        if x[0] == dmin:
            Cp = Cp + [x[1]]
    return dmin, Cp


def ScoreCertificate(T, l):
    M = 0
    for p in l:
        M = float(M + sum([i^2 for i in ListDegree(T, p)]) * log(p))
    return M


def BestCertificateSize(T, size, rangep):
    M = 0
    Best = []
    dmin, C = FindMinimalCommonDegree(T, size, rangep)
    N = Infinity
    for c in C:
        M = ScoreCertificate(T, c)
        if M < N:
            N = M
            Best = c
    return dmin, Best, N


def BestCertificate(T, ranges, rangep):
    N = Infinity
    dmin = -Infinity
    Best = []
    for i in range(1, ranges + 1):
        d, C, M = BestCertificateSize(T, i, rangep)
        if d > dmin:
            dmin = d
            N = M
            Best = C
        elif d == dmin:
            if M < N:
                N = M
                Best = C
    return dmin, Best, N


def CauchyBoundScale(l, s):
    m = len(l)
    an = l[-1]
    aux = [abs(l[i]/an) * s^(i - (m - 1) + 1) for i in range(m - 1)]
    return (s + max(aux))


def CauchyBoundScaleOpt(l):
    B = Infinity
    j = 0
    n = len(l) - 1
    an = l[-1]
    S = max([float((abs(l[i]/an) * (n - i - 1)) ^ (1 / (n - i))) for i in range(n)])
    for i in range(1, ceil(S * 4)):
        if CauchyBoundScale(l, i / 4) < B:
            B = CauchyBoundScale(l, i / 4)
            j = i/4
    return j, B


def FindPrimeFactorLPFW(f, B, d, k):
    t = ceil(B + 1)
    m = 0
    flagC = 0
    prime = Infinity
    rangeL = []
    cont = 0
    for i in range(t, t + k):
        rangeL = rangeL + [i, -i]
    for i in rangeL:
        cont = cont + 1
        sB = (abs(i) - B) ^ d
        V = abs(f(i))
        F = factor(V)
        for p in F:
            if V / (p[0]) < sB and p[0] < prime:
                flagC = 1
                prime = p[0]
                m = i
                break
    if flagC == 1:
        return True, m, prime
    else:
        return False, 0, 0


def CertificateIrrModpFFP(f, p, N):
    """Certificate of irreducibility for f mod p using Rabin's test (with degree factoring).
    Returns a Lean string for a term of type CertificateIrreducibleZModOfList'."""
    R.<X> = PolynomialRing(GF(p))
    f = R(f.list())
    s = p.bit_length() - 1
    binary_list = [int(bit) for bit in bin(p)[2:]]
    bit = binary_list[::-1]
    n = f.degree()
    F = factor(n)
    P = [x[0] for x in F]
    E = [x[1] for x in F]

    if n == 1:
        h = [X, X]
        gaux = [(X^p - X)/f]
    else:
        h = [X] + [0 for i in range(n)]
        gaux = [0 for i in range(n)]
        for i in range(n):
            gaux[i], h[i+1] = (h[i] ^ p).quo_rem(f)

    hprime = [[] for i in range(n)]
    gprime = [[] for i in range(n)]
    for i in range(n):
        hp, gp = sqpow(h[i], f, p)
        hprime[i] = hp
        gprime[i] = gp

    a = [0 for i in range(n)]
    b = [0 for i in range(n)]
    d = [0 for i in range(n)]
    for x in P:
        d[n // x], a[n // x], b[n // x] = xgcd(f, h[n // x] - X)

    h = [list(h[i]) for i in range(n + 1)]
    hprime = [[list(R(hprime[i][j])) for j in range(s+1)] for i in range(n)]
    g = [[list(R(gprime[i][j])) for j in range(s)] for i in range(n)]
    a = [list(R(a[i])) for i in range(n)]
    b = [list(R(b[i])) for i in range(n)]

    if n == 1:
        hprime[0][0] = [0, 1]
        g[0][0] = (R((R(hprime[0][1]) ^ 2 * X ^ (bit[0]) - X) / f)).list()

    strg = ", ".join('!' + str(g[i]) for i in range(len(g)))
    strh = ", ".join('!' + str(hprime[i]) for i in range(len(hprime)))

    out = f"def P{p}P{N} : CertificateIrreducibleZModOfList' {p} {n} 2 {s} {f.list()} where\n"
    out += f" m := {len(P)}\n"
    out += f" P := !{P}\n"
    out += f" exp := !{E}\n"
    out += " hneq := by decide\n"
    out += " hP := by decide\n"
    out += " hlen := by decide\n"
    out += " htr := by decide\n"
    out += f" bit := !{bit}\n"
    out += " hbits := by decide\n"
    out += f" h := !{h}\n"
    out += " g := ![" + strg + "]\n"
    out += " h' := ![" + strh + "]\n"
    out += " hs := by decide\n"
    out += " hz := by decide\n"
    out += " hmul := by decide\n"
    out += f" a := !{a}\n"
    out += f" b := !{b}\n"
    out += " hhz := by decide\n"
    out += " hhn := by decide\n"
    out += " hgcd := by decide\n"
    return out


def GlobalCertificateIrrF(T, lprimes):
    """Lean certificate for irreducibility via degree analysis.
    Returns a string for a term of type IrreducibleCertificateIntPolynomial."""
    m = [len(factorLists(T, p)) for p in lprimes]
    out = "noncomputable def C : IrreducibleCertificateIntPolynomial T l where\n"
    out += " hpol := T_ofList'\n"
    out += f" n := {len(lprimes)}\n"
    out += f" d := {T.degree()}\n"
    out += " hprim := by decide\n"
    out += " hdeg := by decide\n"
    out += " hnn := by decide\n"
    out += " hdn := by decide\n"
    out += f" p := !{lprimes}\n"
    out += " hp := by\n"
    out += "  intro i\n"
    out += "  fin_cases i\n"
    for p in lprimes:
        out += f"  exact hp{p}'.out\n"
    out += f" hlc := by decide\n"
    out += f" m := !{m}\n"
    out += " F := fun i =>\n"
    out += "  match i with\n"
    for i in range(len(lprimes)):
        out += f"  | {i} => !{factorLists(T, lprimes[i])}\n"
    out += " D := fun i =>\n"
    out += "  match i with\n"
    for i in range(len(lprimes)):
        out += f"  | {i} => !{[len(factorLists(T, lprimes[i])[j]) - 1 for j in range(m[i])]}\n"
    out += " hl := by decide\n"
    out += " hirr := by\n"
    out += "  intro i j\n"
    # `<;>` is only needed when `fin_cases i` leaves more than one goal;
    # with a single prime it is redundant and the style linter says so.
    out += ("  fin_cases i <;> fin_cases j\n" if len(lprimes) > 1
            else "  fin_cases i; fin_cases j\n")
    for p in lprimes:
        F = factor(T.change_ring(GF(p)))
        for i in range(len(F)):
            if F[i][0].degree() == 1:
                for j in range(F[i][1]):
                    out += f"  · exact irreducible_ofList_of_linear (R := ZMod {p}) _ (by decide) rfl\n"
            else:
                for j in range(F[i][1]):
                    out += f"  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P{p}PI{i}\n"
    out += " hm := by decide\n"
    out += " hprod := by decide\n"
    out += " hinter := by decide\n"
    return out


def GlobalCertificateLPFWDegree(T, lprimes, dmin, scaling_factor, rho, M, prime):
    """Lean certificate for irreducibility via LPFW with degree analysis.
    Returns a string for a term of type CertificateIrreducibleIntOfPrimeDegreeAnalysis."""
    l = T.list()
    s = abs(T(M)) / prime
    m = [len(factorLists(T, p)) for p in lprimes]

    out = "noncomputable def C : CertificateIrreducibleIntOfPrimeDegreeAnalysis T l where\n"
    out += " hpol := T_ofList'\n"
    out += " hdeg := by decide\n"
    out += " hprim := by decide\n"
    out += f" n := {len(lprimes)}\n"
    out += f" d := {dmin}\n"
    out += f" s := {s}\n"
    out += f" P := {prime}\n"
    out += f" M := {M}\n"
    out += f" r := {scaling_factor}\n"
    out += f" ρ := {rho}\n"
    if floor(log(prime, 10) + 1) < 7:
        out += " hPPrime := by norm_num\n"
    else:
        out += " hPPrime := sorry -- Consider using Pratt certificate\n"
        print(f"ERROR: 'sorry' used for hPPrime in declaration 'C' -- prime {prime} has "
              f"{floor(log(prime, 10) + 1)} digits, too large for norm_num. Proof is incomplete.")
    out += " hrpos := by norm_num\n"
    out += " hnn := by decide\n"
    out += " hdn := by decide\n"
    out += f" p := !{lprimes}\n"
    out += " hp := by\n"
    out += "  intro i\n"
    out += "  fin_cases i\n"
    for p in lprimes:
        out += f"  exact hp{p}'.out\n"
    out += f" hlc := by decide\n"
    out += f" m := !{m}\n"
    out += " F := fun i =>\n"
    out += "  match i with\n"
    for i in range(len(lprimes)):
        out += f"  | {i} => !{factorLists(T, lprimes[i])}\n"
    out += " D := fun i =>\n"
    out += "  match i with\n"
    for i in range(len(lprimes)):
        out += f"  | {i} => !{[len(factorLists(T, lprimes[i])[j]) - 1 for j in range(m[i])]}\n"
    out += " hl := by decide\n"
    out += " hirr := by\n"
    out += "  intro i j\n"
    # `<;>` is only needed when `fin_cases i` leaves more than one goal;
    # with a single prime it is redundant and the style linter says so.
    out += ("  fin_cases i <;> fin_cases j\n" if len(lprimes) > 1
            else "  fin_cases i; fin_cases j\n")
    for p in lprimes:
        F = factor(T.change_ring(GF(p)))
        for i in range(len(F)):
            if F[i][0].degree() == 1:
                for j in range(F[i][1]):
                    out += f"  · exact irreducible_ofList_of_linear (R := ZMod {p}) _ (by decide) rfl\n"
            else:
                for j in range(F[i][1]):
                    out += f"  · dsimp ; exact irreducible_ofList_ofCertificateIrreducibleZModOfList' P{p}PI{i}\n"
    out += " hm := by decide\n"
    out += " hprod := by decide\n"
    out += " hinter := by decide\n"
    out += " hrhoeq := by decide\n"
    out += " hrho := by decide\n"
    out += " hs := by norm_num\n"
    out += " heval := by norm_num\n"
    return out


def GlobalCertificateLPFW(T, scaling_factor, rho, M, prime):
    """Lean certificate for irreducibility via LPFW without degree analysis.
    Returns a string for a term of type CertificateIrreducibleIntOfPrime."""
    s = abs(T(M)) / prime
    out = "noncomputable def C : CertificateIrreducibleIntOfPrime T l where\n"
    out += " hpol := T_ofList'\n"
    out += " hdeg := by decide\n"
    out += " hprim := by decide\n"
    out += " hlz := by decide\n"
    out += f" s := {s}\n"
    out += f" P := {prime}\n"
    out += f" M := {M}\n"
    out += f" r := {scaling_factor}\n"
    out += f" ρ := {rho}\n"
    if floor(log(prime, 10) + 1) < 7:
        out += " hPPrime := by norm_num\n"
    else:
        out += " hPPrime := sorry -- Consider using Pratt certificate\n"
        print(f"ERROR: 'sorry' used for hPPrime in declaration 'C' -- prime {prime} has "
              f"{floor(log(prime, 10) + 1)} digits, too large for norm_num. Proof is incomplete.")
    out += " hrpos := by norm_num\n"
    out += " hrhoeq := by decide\n"
    out += " hrho := by decide\n"
    out += " hs := by norm_num\n"
    out += " heval := by norm_num\n"
    return out


def LeanProofIrreducible(T):
    """Produces a complete Lean proof of irreducibility for T.
    Returns the Lean file content as a string."""
    flagP = 0
    dmin = 0
    l = T.list()
    T_lean = str(T).replace('x', 'X')
    scaling_factor, rho = CauchyBoundScaleOpt(l)
    flag, M, prime = FindPrimeFactorLPFW(T, rho, 1, 20)

    if prime != 0 and floor(log(prime, 10) + 1) < 7:
        flagP = 1
    else:
        dmin, lprimes, N = BestCertificate(T, 3, 40)

    if dmin == T.degree() and flagP == 0:
        out = f"""import IdealArithmetic.DedekindProject.Polynomial.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime

open Polynomial

local notation "T" => ({T_lean} : ℤ[X])

local notation "l" => {T.list()}

lemma T_ofList' : T = ofList l := by norm_num ; ring
"""
        for p in lprimes:
            out += f"instance hp{p}' : Fact $ Nat.Prime {p} := fact_iff.2 (by norm_num)\n"
        out += "\n"
        for p in lprimes:
            F = factor(T.change_ring(GF(p)))
            for N in range(len(F)):
                if (F[N][0].degree()) > 1:
                    if N == 0:
                        out += CertificateIrrModpFFP(F.unit() * F[N][0], p, 'I' + str(N))
                        out += "\n"
                    else:
                        out += CertificateIrrModpFFP(F[N][0], p, 'I' + str(N))
                        out += "\n"
        out += GlobalCertificateIrrF(T, lprimes)
        out += "\n"
        out += "theorem irreducible_T : Irreducible T := irreducible_of_CertificateIntPolynomial _ _ C\n"
        return out
    else:
        out = f"""import IdealArithmetic.DedekindProject.Polynomial.IrreduciblePolynomialZModp
import Mathlib.Tactic.NormNum.Prime
import IdealArithmetic.DedekindProject.Polynomial.BrillhartIrreducibilityTest

open Polynomial

local notation "T" => ({T_lean} : ℤ[X])

local notation "l" => {T.list()}

unseal Rat.add Rat.mul Rat.inv

lemma T_ofList' : T = ofList l := by norm_num ; ring
"""
        if flagP == 0:
            flag, M, prime = FindPrimeFactorLPFW(T, rho, dmin, 50)
        if abs(T(M)) / prime >= abs(M) - rho and dmin > 1 and flagP == 0:
            for p in lprimes:
                out += f"instance hp{p}' : Fact $ Nat.Prime {p} := fact_iff.2 (by norm_num)\n"
            out += "\n"
            for p in lprimes:
                F = factor(T.change_ring(GF(p)))
                for N in range(len(F)):
                    if (F[N][0].degree()) > 1:
                        if N == 0:
                            out += CertificateIrrModpFFP(F.unit() * F[N][0], p, 'I' + str(N))
                            out += "\n"
                        else:
                            out += CertificateIrrModpFFP(F[N][0], p, 'I' + str(N))
                            out += "\n"
            out += GlobalCertificateLPFWDegree(T, lprimes, dmin, scaling_factor, rho, M, prime)
            out += "\n"
            out += "theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrimeDegrees _ _ C\n"
            return out
        else:
            out += GlobalCertificateLPFW(T, scaling_factor, rho, M, prime)
            out += "\n"
            out += "theorem irreducible_T : Irreducible T := irreducible_of_CertificateIrreducibleIntOfPrime _ _ C\n"
            return out

def write_irreducible_lean(T, out_file='Irreducible.lean', native=False):
    """Write the Lean irreducibility proof of T and return it.

    T        : polynomial in ZZ['x'], or anything ZZ['x'] accepts
    out_file : path of the file to write, or an open file handle, as the
               `doc` argument of the original script
    native   : emit `native_decide` for the fields closed by `decide`
    """
    T = ZZ['x'](T)
    text = _retactic(LeanProofIrreducible(T), native)
    if hasattr(out_file, 'write'):
        out_file.write(text)
        return text
    folder = os.path.dirname(out_file)
    if folder:
        os.makedirs(folder, exist_ok=True)
    with open(out_file, 'w') as fh:
        fh.write(text)
    print(f'Wrote {out_file}' + ('  [native_decide]' if native else ''))
    return text
