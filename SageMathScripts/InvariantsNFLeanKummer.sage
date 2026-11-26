# Single-file Sage script for Lean class group certificates
# Entry point: generate_invariants_proof_lean_kummer(T, B_polys, num)
#
# Usage example (degree 3):
#
#   load('InvariantsNFLeanKummer.sage')
#   R.<x> = PolynomialRing(ZZ)
#   f = x^3 + 150*x - 50
#   K.<a> = NumberField(f)
#   B = [1, a, 1/5*a^2]          # integral basis of K
#   label = '3_1_542700_3'       # names the output folder NF<label> and the files in it
#   generate_invariants_proof_lean_kummer(f, B, label)
#
# This writes only .lean files (Irreducible/RI/PrimesBelow*/ClassGroupData/
# ClassGroupSaturated*/RelationIdeals*/Invariants/Results) into ./NF<label>/.
#
# This version incorporates Kummer-Dedekind and is adapted from
# https://github.com/alainchmt/CertifyingInvariantsNF/blob/v1/InvariantsNFLean.sage
# with the help of Claude Code (Opus 5).


from itertools import combinations
import itertools
import os

load('InvariantsNFLean.sage')

# =============================================================================
# Kummer-Dedekind fork.
#
# For a prime `p` coprime to the common denominator `d` of the subalgebra
# construction, the ideals above `p` can be produced directly from the
# factorisation of `T mod p` (see below), instead of via
# `gens_reduced()` + the minimal-polynomial primality certificate. For `p | d`
# the classical route is still needed, so these fall back to the existing
# `PrimesBelowGens`/`PrimesBelowBound` unchanged.
#
# Nothing above this line is modified; everything below is additive.
# =============================================================================

import re

# =============================================================================
# For Kummer-Dedekind prime-ideal data.
#
# Given a defining polynomial `T` for a number field and an integral basis `B`,
# and a prime `p` coprime to the common denominator `d` of the subalgebra
# construction, this emits a Lean block for the primes above `p`, matching the
# naming convention and `KummerData` usage hand-written for `p = 2` in
# `IdealArithmetic/Examples/NF3_1_24215_1/PrimesBelow3_1_24215_1F0.lean`:
#
#   instance hp{p} : Fact (Nat.Prime p)
#   I{p}N{i} : Ideal O            -- one per *distinct* irreducible factor
#   P{p}P{i} : CertificateIrreducibleZModOfList' ...
#   A{p}     : FactorsPolyZMod l p m
#   C{p}{i}  : PrimeIdealKummer Table a z (A{p}.D k) p
#   K{p}     : KummerData p ![...] ![...]
#
# `A{p}`'s `D`/`n`/`hirr` are indexed *with multiplicity* (`m` = sum of the
# exponents), since that's what `FactorsPolyZMod` requires. But `I{p}N{i}` and
# `P{p}P{i}`/`C{p}{i}` are indexed by *distinct* factor: for a repeated factor,
# `A{p}.D k` at each of its multiplicity slots `k` is definitionally the same
# list, so the one certificate/ideal built for it is reused at every such slot
# rather than re-emitted. This also keeps the naming aligned with
# `PrimesBelowGens`'s own convention (one entry per distinct prime factor),
# which is what the rest of `InvariantsNFLean.sage` expects downstream.
# =============================================================================


def _indent_block(text, k):
    pad = " " * k
    return "\n".join(pad + line if line else line for line in text.split("\n"))


def _match_dispatch(names, indent):
    """`match i with | 0 => exact <names[0]> | 1 => exact <names[1]> | ...`,
    the dispatch style used by hand for `hirr` and for `KummerData`'s `C` field
    (in place of the `fin_cases`/`Fin.cases` combinators used elsewhere: those
    fields hold *data*, not proofs, so `fin_cases` cannot eliminate them, and a
    flat `match` reads closer to what was hand-written than a `Fin.cases` chain)."""
    pad = " " * indent
    lines = ["intro i", "match i with"]
    lines += ["| %s => exact %s" % (i, n) for i, n in enumerate(names)]
    return "\n".join(pad + l for l in lines)


def _lift_factor_to_K(g, alpha):
    """The integer lift of a factor of `T mod p`, evaluated at `alpha`."""
    return sum(ZZ(c) * alpha ** k for k, c in enumerate(g.list()))


def KummerFactorsData(K, T, B, p):
    """Compute everything needed for the Lean terms.

    Returns a dict keyed both *with multiplicity* (`D`, `degs`, ... indexed by
    `m` = sum of exponents, for `FactorsPolyZMod`) and by *distinct* factor
    (`distinct_D`, `distinct_degs`, ..., indexed by the number of distinct
    irreducible factors, for `I{p}N{i}`/`P{p}P{i}`/`C{p}{i}`), plus
    `flat_to_distinct`, mapping each with-multiplicity slot to its distinct
    factor's index.
    """
    p = ZZ(p)
    if not p.is_prime():
        raise ValueError("p must be prime")
    alpha = K.gen()
    Rp = PolynomialRing(GF(p), 'Y')
    Tp = Rp(T.list())

    grouped = list(factor(Tp))                       # [(g, e), ...], distinct
    factors = []                                      # flat, with multiplicity
    flat_to_distinct = []
    for i, (g, e) in enumerate(grouped):
        factors += [g] * e
        flat_to_distinct += [i] * e

    distinct = [g for g, e in grouped]
    z = (elems_to_basis([K(1)], B)).list()
    a = (elems_to_basis([alpha], B)).list()
    w0 = [p * c for c in z]
    distinct_w1 = [(elems_to_basis([_lift_factor_to_K(g, alpha)], B)).list() for g in distinct]

    return {
        'p': p,
        'm': len(factors),
        'flat_to_distinct': flat_to_distinct,
        'D': [[ZZ(c) for c in g.list()] for g in factors],
        'degs': [g.degree() for g in factors],
        's': p.bit_length() - 1,
        'z': z,
        'a': a,
        'w0': w0,
        'distinct_factors': distinct,
        'distinct_mult': [e for g, e in grouped],
        'distinct_D': [[ZZ(c) for c in g.list()] for g in distinct],
        'distinct_degs': [g.degree() for g in distinct],
        'distinct_w1': distinct_w1,
    }


def KummerPrimeBlockLean(K, T, B, p, d=1, l_name=None, have_fact=False):
    """Lean source for the primes above `p`, in the hand-written style:
    `instance hp{p}`, `I{p}N{i}`, `P{p}P{i}`, `A{p}`, `C{p}{i}`, `K{p}`.

    `d` is the common denominator of the subalgebra construction; `p` must be
    coprime to it (this is exactly the hypothesis `conductor_hroot_coprime`
    needs to discharge `hcond`, via `by decide` on `Int.gcd d p = 1`).

    `l_name` is what to print for the coefficient list of `T`.  It defaults to
    the literal list, since the example files declare `l` as *local* notation,
    which is not visible to importing files.

    `have_fact`: set to `True` if `Fact (Nat.Prime p)` is already in scope (as
    happens for primes reused from the ring-of-integers certification in the
    `RI...` file, e.g. `hp5`/`hp29`/`hp167` in `NF3_1_24215_1`) -- otherwise
    the emitted `instance hp{p}` would collide with the existing one.
    """
    D = KummerFactorsData(K, T, B, p)
    p, m = D['p'], D['m']
    nd = len(D['distinct_factors'])
    if gcd(ZZ(d), p) != 1:
        raise ValueError("p = %s is not coprime to d = %s; conductor_hroot_coprime "
                          "cannot be discharged for this prime" % (p, d))

    a_lit = "!%s" % D['a']
    z_lit = "!%s" % D['z']
    l_name = l_name or str(T.list())

    out = "\n"

    if not have_fact:
        out += "\ninstance hp%s : Fact (Nat.Prime %s) := {out := by norm_num}\n" % (p, p)

    # ---- the ideals, one literal two-generator span per distinct factor ----
    for i in range(nd):
        out += "\ndef I%sN%s : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm " \
               "(![!%s, !%s] i)))\n" % (p, i, D['w0'], D['distinct_w1'][i])

    # ---- irreducibility certificates, one per distinct factor ---------------
    for i, g in enumerate(D['distinct_factors']):
        out += "\n" + CertificateIrrModpFFP(g, p, i)

    # ---- the FactorsPolyZMod term (with multiplicity) ------------------------
    out += "\ndef A%s : FactorsPolyZMod %s %s %s where\n" % (p, l_name, p, m)
    lists = "![" + ", ".join(str(dl) for dl in D['D']) + "]"
    out += " D := %s; D' := %s\n" % (lists, lists)
    out += " heqm := by decide\n"
    out += " hProd := by decide\n"
    out += " s := !%s\n" % ([D['s']] * m)
    out += " n := !%s; t := 2\n" % D['degs']
    out += " hn := by intro i; fin_cases i <;> exact ⟨by decide⟩\n"
    out += " hirr := by\n"
    hirr_names = ["P%sP%s" % (p, D['flat_to_distinct'][k]) for k in range(m)]
    out += _match_dispatch(hirr_names, 2) + "\n"

    # ---- the PrimeIdealKummer terms, one named `where` def per distinct factor
    for i in range(nd):
        out += "\ndef C%s%s : PrimeIdealKummer Table %s %s (A%s.D %s) %s where\n" % (
            p, i, a_lit, z_lit, p, i, p)
        out += "  n := %s\n" % D['distinct_degs'][i]
        out += "  w := ![!%s, !%s]\n" % (D['w0'], D['distinct_w1'][i])
        out += "  hpmem := by decide\n"
        out += "  hlen := by decide\n"
        out += "  hpol := by decide\n"

    # ---- the KummerData term, bundling everything above (with multiplicity) -
    Is = "![" + ", ".join("I%sN%s" % (p, D['flat_to_distinct'][k]) for k in range(m)) + "]"
    Ns = "![" + ", ".join(str(p ** D['degs'][k]) for k in range(m)) + "]"
    out += "\ndef K%s : KummerData %s %s %s where\n" % (p, p, Is, Ns)
    out += "  a := %s\n" % a_lit
    out += "  z := %s\n" % z_lit
    out += "  heq := timesTableT_eq_Table\n"
    out += "  A := A%s\n" % p
    out += "  C := by\n"
    c_names = ["C%s%s" % (p, D['flat_to_distinct'][k]) for k in range(m)]
    out += _match_dispatch(c_names, 4) + "\n"
    out += "  hmin := minpoly_hroot\n"
    out += "  hcond := conductor_hroot_coprime %s (by decide)\n" % p
    out += "  hBz := B_one_repr\n"
    out += "  hieq := by\n"
    out += "    intro i\n"
    out += "    fin_cases i <;> rfl\n"
    out += "  hN := by decide\n"
    return out


# =============================================================================
# Test invocation: the field of NF3_1_24215_1, primes above 2 and 3.
# =============================================================================
if __name__ == '__main__':
    Rz.<X> = PolynomialRing(ZZ)
    T = X ^ 3 + 17 * X - 13
    K.<alpha> = NumberField(T)
    B = [K(1), alpha, alpha ^ 2]

    for p in [2, 3]:
        print(KummerPrimeBlockLean(K, T, B, p, d=1))


def PrimesBelowGensKummer(K, T, B, p, d):
    """Like `PrimesBelowGens`, but for `p` coprime to `d` returns the
    Kummer-Dedekind generators `[p, D_i(alpha)]`, one entry per distinct
    irreducible factor of `T mod p` (always 2 generators, even if the ideal
    happens to be principal). Delegates the factorisation itself to
    `KummerFactorsData`, the same call `KummerPrimeBlockLean` uses to name
    `I{p}N{i}` -- Sage's `factor()` over `GF(p)` isn't guaranteed to return
    factors in the same order across independent calls, so a second,
    separate `factor()` here could silently disagree with which distinct
    factor is `I{p}N{i}`."""
    set_random_seed(10)  # match PrimesBelowGens's own reset, so later randomized
    p = ZZ(p)             # calls (e.g. K.class_group(proof=False)) stay reproducible
    if gcd(ZZ(d), p) != 1:
        return PrimesBelowGens(K, p)
    alpha = K.gen()
    Df = KummerFactorsData(K, T, B, p)
    return [[[K(p), _lift_factor_to_K(g, alpha)], e, 0]
            for g, e in zip(Df['distinct_factors'], Df['distinct_mult'])]


def PrimesBelowBoundKummer(K, B, T, d, M1, M2, list_exclude, primes_below_gens):
    """Like `PrimesBelowBound`, but for primes coprime to `d` emits a
    `KummerData` block (`K{p}`) instead of the certificate + chain-
    multiplication proof of `ContainsPrimesAboveP`. Primes dividing `d` fall
    back to `PrimesBelowBound`, called one prime at a time so its body stays
    untouched -- reusing the same cached `primes_below_gens` (rather than a
    fresh `PrimesBelowGens(K, q)` call) is required: `.gens_reduced(proof=False)`
    is randomized, so a second, independent call can pick different generator
    representatives for the same ideal, which would desync these `I{p}N{i}`
    definitions from the ones `RelationsGeneratorIntervalKummer` certifies
    against."""
    out = ""
    for p in primes(M1, M2 + 1):
        if gcd(ZZ(d), p) == 1:
            out += KummerPrimeBlockLean(K, T, B, p, d=d, have_fact=(p in list_exclude))
        else:
            out += PrimesBelowBound(K, B, p, p, list_exclude, primes_below_gens)
    return out


def PrimesBelowBoundCertificteGenIntervalKummer(K, B, T, d, M, number_interval,
                                                 primes_below_gens, interval_size=None):
    """Like `PrimesBelowBoundCertificteGenInterval`, but for primes coprime to
    `d` patches the `hC`/`hN` branches to `convert (containsPrimesAbove_of_KummerData K{p})`
    / `exact (card_quot_of_KummerData K{p})`. `primes_below_gens` must already
    return Kummer-Dedekind generators for those primes (e.g. a closure over
    `PrimesBelowGensKummer`), so norms/names come out consistent with `K{p}`."""
    res = PrimesBelowBoundCertificteGenInterval(K, B, M, number_interval, primes_below_gens, interval_size)
    interval_strings = list(res[0])
    for p in primes(M):
        if gcd(ZZ(d), p) != 1:
            continue
        hN_pat = re.compile(r'    · dsimp ; intro j\n      fin_cases j\n(?:      exact NI%sN\d+\n)+' % p)
        for j in range(len(interval_strings)):
            s = interval_strings[j]
            s = s.replace('    · exact PBC%s\n' % p,
                           '    · convert (containsPrimesAbove_of_KummerData K%s) <;> rfl\n' % p)
            s = hN_pat.sub('    · exact (card_quot_of_KummerData K%s)\n' % p, s, count=1)
            interval_strings[j] = s
    return (interval_strings,) + res[1:]


def LeanProofKummer(T, basis, nameIrr, num, comment, flagD):
    """Like `LeanProof`, but also emits the imports and lemmas (`hroot_coord`,
    `minpoly_hroot`, `conductor_hroot_coprime`) that `K{p}` blocks need."""
    out, bad, flagl, flaglW, flagD = LeanProof(T, basis, nameIrr, num, comment, flagD)
    out = out.replace(
        "import IdealArithmetic.DedekindProject.CertifyRingOfIntegers",
        "import IdealArithmetic.DedekindProject.CertifyRingOfIntegers\n"
        "import IdealArithmetic.ConductorSubalgebraBuilder\n"
        "import IdealArithmetic.PrimeIdealsKummer", 1)
    C, denom = BasisToMatrix(basis)
    _, _, auxTemp = SubalgebraBuilderF(T, C, denom)
    a_lit = "!%s" % auxTemp.list()
    out += f"""
lemma hroot_coord :
    timesTableO.basis.equivFun.symm {a_lit} = ⟨θ, hroot_mem⟩ :=
  root_coord_subalgebraBuilder BQ {a_lit} [] (by decide)

lemma minpoly_hroot :
    minpoly ℤ (timesTableO.basis.equivFun.symm {a_lit}) = ofList l := by
  rw [hroot_coord]
  exact minpoly_root_subalgebra BQ hroot_mem

lemma conductor_hroot_coprime (p : ℕ) (gcd : Int.gcd BQ.d p = 1) :
    Ideal.comap (algebraMap ℤ O) (conductor ℤ (timesTableO.basis.equivFun.symm {a_lit}))
      ⊔ Ideal.span {{(p : ℤ)}} = ⊤ := by
  rw [hroot_coord]
  exact conductor_coprime_of_coprime_int BQ hroot_mem p gcd
"""
    return out, bad, flagl, flaglW, flagD


def PowAllZeroLean(B, s):
    """The `Pow...` lemma for the all-zero exponent tuple, `J0^0*...*J{s-1}^0
    = (1)` (`(1 : Ideal O)` itself when `s = 0`). `ClassGroupDataLean`'s own
    loop skips this tuple as trivial, but a Kummer-Dedekind-represented prime
    ideal that happens to be principal still needs it (see
    `RelationsGeneratorIntervalKummer`). Returns (name, lean_str)."""
    name = 'PowUnit' if s == 0 else 'Pow' + ''.join(f'J{i}_0' for i in range(s))
    lhs = '(1 : Ideal O)' if s == 0 else '*'.join(f'J{i} ^ 0' for i in range(s))
    coord = ExList(str([[1] + [0] * (len(B) - 1)]))
    simp_lemmas = (['pow_zero', 'one_mul'] if s > 0 else []) + ['Set.range_unique', 'Matrix.cons_val_fin_one']
    out = f"\nlemma {name} : {lhs} = Ideal.span (Set.range fun i ↦ B.equivFun.symm ({coord} i)) := by\n"
    out += f" simp only [{', '.join(simp_lemmas)}]\n"
    out += " rw [B_one_repr, Ideal.span_singleton_one, Ideal.one_eq_top]\n"
    return name, out


def RelationsGeneratorIntervalKummer(K, B, M1, M2, J_ideal_gens, J_name, name_cert,
                                      generators_vec, primes_below_gens, minkowski_bound,
                                      class_group, is_kummer):
    """Like `RelationsGeneratorInterval`, but also emits a relation certificate
    when `is_kummer(p)` even if the ideal is principal (`expon` all zero):
    Kummer-Dedekind primes always carry two generators, so
    `ClassGroupOrderProofSplit` always expects an `R{p}N{i}` for them, unlike
    the flag-based single-generator case that `name_cert_alt` special-cases
    away as `rfl`. `s = 0` (trivial class group) is handled directly, since
    `RelationsGeneratorInterval` never exercises it (its gate always skips)."""
    s = len(J_ideal_gens)
    BM = []
    O = K.ring_of_integers()
    J_name_list = [J_name + str(i) for i in range(s)]
    J = [K.ideal(J_ideal_gens[i]) for i in range(s)]
    out = ""
    for p in primes(M1, M2 + 1):
        F = primes_below_gens(p)
        l = len(F)
        BMp = []
        for cont in range(l):
            I = K.ideal(F[cont][0])
            if I.norm() < minkowski_bound:
                expon = [(class_group(I)).exponents()[i] for i in range(s)]
                BMp.append(expon)
                if expon != [0 for i in range(s)] or is_kummer(p):
                    set_random_seed(10)
                    JJ = prod([J[i]**(expon[i]) for i in range(s)]) if s > 0 else K.ideal(1)
                    genel = (I / JJ).gens_reduced(proof=False)[0]
                    d = genel.denominator()
                    for t_p in prime_divisors(d):
                        while (d % t_p == 0) and ((d // t_p) * genel in O):
                            d = d // t_p
                    x = d * genel

                    alpha = elems_to_basis([x], B).list()
                    JJ_gens_reduced = generators_vec([expon[i] for i in range(s)])
                    A = [x * i for i in JJ_gens_reduced]
                    C = ([d * i for i in F[cont][0]])
                    CC = F[cont][0]

                    Gen1 = [elems_to_basis(A, B).transpose().rows()[j].list() for j in range(len(A))]
                    Gen2 = [elems_to_basis(C, B).transpose().rows()[j].list() for j in range(len(C))]
                    before_div = [elems_to_basis(CC, B).transpose().rows()[j].list() for j in range(len(CC))]
                    JJ_gens = [elems_to_basis(JJ_gens_reduced, B).transpose().rows()[j].list() for j in range(len(JJ_gens_reduced))]

                    h = [IdealLift(K, B, C, A[i]) for i in range(len(A))]
                    g = [IdealLift(K, B, A, C[i]) for i in range(len(C))]

                    gp = [[elems_to_basis(g[i], B).transpose().rows()[j].list() for j in range(len(A))] for i in range(len(g))]
                    hp = [[elems_to_basis(h[i], B).transpose().rows()[j].list() for j in range(len(C))] for i in range(len(h))]

                    if s == 0:
                        J_name_exp = '(1 : Ideal O)'
                    elif s < 2:
                        J_name_exp = J_name_list[0] + f' ^ {expon[0]}'
                    else:
                        J_name_exp = J_name_list[0] + f' ^ {expon[0]}'
                        for i in range(1, s):
                            J_name_exp = J_name_exp + '*' + J_name_list[i] + f'^ {expon[i]}'

                    cont2 = cont

                    out += f"""

noncomputable def E{p}RS{cont} : RelationCertificate Table {d} {ExList(str(before_div))}
  !{alpha} {ExList(str(JJ_gens))} where
    su := {ExList(str(Gen2))}
    hsu := by decide
    w := {ExList(str(Gen1))}
    hw := by decide
    g := {ExList(str(gp))}
    h := {ExList(str(hp))}
    hle1 := by decide
    hle2 := by decide

lemma R{p}N{cont} : Ideal.span {{{d}}} * I{p}N{cont2} =  Ideal.span {{B.equivFun.symm !{alpha}}} * ({J_name_exp}) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl {name_cert(expon)} E{p}RS{cont} \n"""
        BM = BM + [BMp]
    return out, BM


def generate_invariants_proof_lean_kummer(T, B_polys, num, out_dir='.', lean_root=None, wrap_ns=True):
    """Generate all Lean files for the class group certificate.

    T       : irreducible polynomial in ZZ['x']
    B_polys : list of elements of NumberField(T, 'a') forming the integral basis
    num     : label string for the output directory and file names
    """
    global LEAN_ROOT
    if lean_root is not None:
        LEAN_ROOT = lean_root
    # The Dedekind certificate needs an *integer* Bezout pair; over QQ[x] the gcd is 1
    # and the cofactors are rational, which silently produces an invalid certificate.
    T = ZZ['x'](T)

    K = None
    if len(B_polys) > 1 and hasattr(B_polys[1], 'parent'):
        parent0 = B_polys[1].parent()
        if hasattr(parent0, 'number_field'):
            # parent0 is an order (e.g. from K.maximal_order().basis()); recover the field.
            K = parent0.number_field()
        elif isinstance(parent0, NumberField_base):
            K = parent0
    if K is None:
        K = NumberField(T, 'a')
    B = B_polys
    T_lean = str(T).replace('x', 'X')
    _, d = BasisToMatrix(B)  # common denominator; d = 1 unless a scaled basis is used

    folder = os.path.join(out_dir, f"NF{num}")
    os.makedirs(folder, exist_ok=True)

    # 1. Irreducible{num}.lean
    irr_str = LeanProofIrreducible(T)
    with open(f"{folder}/Irreducible{num}.lean", "w") as f:
        f.write(_wrap_ns(irr_str, num, wrap_ns))

    # 2. RI{num}.lean (ring of integers)
    ri_str, bad, flagl, flaglW, flagD = LeanProofKummer(T, B, f'Irreducible{num}', num, '', 1)
    with open(f"{folder}/RI{num}.lean", "w") as f:
        f.write(_wrap_ns(ri_str, num, wrap_ns))

    # 3. Global numeric data
    disc_factors = [factor(T.discriminant())[i][0]
                    for i in range(len(factor(T.discriminant())))]
    M = K.minkowski_bound()
    bound = floor(M + 0.01) + 1
    PP = list(primes(bound))
    m = len(PP)
    NI = ceil(20 / harmonic_number(K.degree()))
    NF = ceil(m / NI)
    D = K.discriminant()

    # Precompute PrimesBelowGens for all primes up to bound
    pbg_list = [0] * (bound + 1)
    for p in PP:
        pbg_list[p] = PrimesBelowGensKummer(K, T, B, p, d)

    def primes_below_gens(p):
        return pbg_list[p]

    # 4. PrimesBelow{num}F{i}.lean + PrimesBelowCert{num}.lean
    interval_strings, gluing_string, listIint, listPint, listI, listP = \
        PrimesBelowBoundCertificteGenIntervalKummer(K, B, T, d, bound, NF, primes_below_gens, NI)

    for i in range(NF):
        lo = PP[i * NI]
        hi = PP[min((i + 1) * NI - 1, m - 1)]
        header = f"""
import {LEAN_ROOT}.NF{num}.RI{num}
import IdealArithmetic.Generation.ClassGroupGeneration
import IdealArithmetic.IdealArithmetic
import IdealArithmetic.Computation.PrimeSieve

set_option linter.all false

open Classical Polynomial

noncomputable section """
        pb_str = PrimesBelowBoundKummer(K, B, T, d, lo, hi, disc_factors, primes_below_gens)
        with open(f"{folder}/PrimesBelow{num}F{i}.lean", "w") as f:
            f.write(_wrap_ns(header + pb_str + "\n" + interval_strings[i], num, wrap_ns))

    cert_header = "".join(
        f"import {LEAN_ROOT}.NF{num}.PrimesBelow{num}F{i}\n"
        for i in range(NF)
    ) + "\nnoncomputable section"
    if NF > 70:
        cert_header += "\nset_option maxRecDepth 20000"
        cert_header += "\nset_option maxHeartbeats 400000"
    with open(f"{folder}/PrimesBelowCert{num}.lean", "w") as f:
        f.write(_wrap_ns(cert_header + gluing_string, num, wrap_ns))

    # 5. Class group data
    # Computed with proof=False (i.e. assuming GRH) rather than under Sage's default
    # provably-correct mode, which can be orders of magnitude slower.
    O = K.ring_of_integers()
    Cl = K.class_group(proof=False)
    num_gens = len(list(Cl.gens()))
    ideal_gens = [Cl.gens()[i].ideal().gens_reduced(proof=False) for i in range(num_gens)]
    J = [K.ideal(ideal_gens[i]) for i in range(num_gens)]
    t_orders = [Cl(J[i]).order() for i in range(num_gens)]
    # x[i] must be the exact value IdealPowLean will independently recompute for
    # J[i]^t_orders[i] (see IdealPowerGenerator) -- not an independently
    # gens_reduced() ideal power, which can land on a different associate.
    x = [IdealPowerGenerator(K, B, ideal_gens[i], t_orders[i])[0] for i in range(num_gens)]
    u = [K(g) for g in K.unit_group(proof=False).gens()]
    primesCN = [factor(prod(t_orders))[i][0]
                for i in range(len(factor(prod(t_orders))))] if t_orders else []

    # 6. ClassGroupData{num}.lean
    set_random_seed(10)
    cg_str, giL, MAux = ClassGroupDataLean(K, B, num, J, ideal_gens, 'J', x, t_orders, u)
    _, allzero_str = PowAllZeroLean(B, num_gens)
    cg_str += allzero_str
    with open(f"{folder}/ClassGroupData{num}.lean", "w") as f:
        f.write(_wrap_ns(cg_str, num, wrap_ns))

    # 7. ClassGroupSaturated{num}_{pr}.lean for each prime
    local_data_sat = []
    for pr in primesCN:
        phi, A, Q, elems, flag = MatrixPrimesG(K, O, pr, x, t_orders, 400)
        elems = [K(r) for r in elems]
        Ql = [list(Q[j].gens()) for j in range(len(Q))]
        Qlq = [Ql[j][0] for j in range(len(Ql))]
        if flag == 0:
            names = [f'zeta{j + 1}' for j in range(len(elems) - len(phi))] + \
                    [f'alpha{phi[j]}' for j in range(len(phi))]
        else:
            names = [f'zeta{j + 1}' for j in range(len(elems) - len(phi) - 1)] + \
                    ['v'] + [f'alpha{phi[j]}' for j in range(len(phi))]
        local_data_sat.append([A, phi, Qlq, names, flag])

        set_random_seed(10)
        sat_import = f"import {LEAN_ROOT}.NF{num}.ClassGroupData{num}\n"
        sat_body = SaturatedCertLean(K, B, num, Ql, pr, elems, names, f'Sat{pr}')
        with open(f"{folder}/ClassGroupSaturated{num}_{pr}.lean", "w") as f:
            f.write(_wrap_ns(sat_import + sat_body, num, wrap_ns))

    # 8. RelationIdeals{num}F{i}.lean
    def name_cert_kummer(l):
        if l == []:
            return 'PowUnit'
        return 'Pow' + ''.join(f'J{i}_{l[i]}' for i in range(len(l)))

    def generators_vec_kummer(l):
        if l == [0] * len(l):
            return [K(1)]
        return MAux[tuple(l)]

    is_kummer = lambda p: gcd(ZZ(d), p) == 1
    any_kummer = any(is_kummer(p) for p in primes(bound))

    BMf = []
    set_random_seed(10)
    for i in range(NF):
        lo = PP[i * NI]
        hi = PP[min((i + 1) * NI - 1, m - 1)]
        rel_out, BMp = RelationsGeneratorIntervalKummer(
            K, B, lo, hi, ideal_gens, 'J',
            name_cert_kummer, generators_vec_kummer, primes_below_gens,
            bound, Cl, is_kummer
        )
        if num_gens > 0 or any_kummer:
            rel_header = f"""import {LEAN_ROOT}.NF{num}.PrimesBelow{num}F{i}
import {LEAN_ROOT}.NF{num}.ClassGroupData{num}

set_option linter.all false

noncomputable section
"""
            with open(f"{folder}/RelationIdeals{num}F{i}.lean", "w") as f:
                f.write(_wrap_ns(rel_header + rel_out, num, wrap_ns))
        BMf += BMp

    BM = [e for sublist in BMf for e in sublist]

    # 9. Invariants{num}.lean
    inv_str = build_invariants_content(
        T, K, B, num, bad, flagl, flaglW, flagD,
        t_orders, ideal_gens, u, primesCN, local_data_sat,
        NF, listIint, listPint, BM, D, num_gens, NI
    )
    # `unfold_prod` (from ExponentiationZMod) is needed whenever an interval mixes
    # Kummer-Dedekind ideals (always flag 0) with old-method principal ideals (flag
    # 1) -- a case the original driver's import selection never had to cover, since
    # flags used to be uniform within an interval.
    extra_imports = "import IdealArithmetic.Computation.ExponentiationZMod\n"
    if num_gens == 0 and any_kummer:
        extra_imports += "".join(
            f"import {LEAN_ROOT}.NF{num}.RelationIdeals{num}F{i}\n"
            for i in range(NF)
        )
    inv_str = inv_str.replace(
        f"import {LEAN_ROOT}.NF{num}.PrimesBelowCert{num}",
        extra_imports + f"import {LEAN_ROOT}.NF{num}.PrimesBelowCert{num}", 1)
    with open(f"{folder}/Invariants{num}.lean", "w") as f:
        f.write(_wrap_ns(inv_str, num, wrap_ns))

    # 10. Results{num}.lean
    t_final = [1] if t_orders == [] else t_orders
    results_str = f"""import {LEAN_ROOT}.NF{num}.Invariants{num}

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `{T_lean}`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) ({T_lean})) := rfl

lemma T_irreducible' : Irreducible ({T_lean} : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'
"""
    if flagD == 1:
        results_str += f"""
theorem K_discr' : discr K = {D} := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = {K.signature()[1]} := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = {K.signature()[0]} := K_nrRealPlaces
"""
    results_str += f"""
def class_group_equiv' :
  (∀ i : Fin {len(t_final)} , (ZMod (!{t_final} i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_{prod(t_final)}' : classNumber K = {prod(t_final)} := class_number_K_eq_{prod(t_final)}
"""
    with open(f"{folder}/Results{num}.lean", "w") as f:
        f.write(_wrap_ns(results_str, num, wrap_ns))

    print(f"Generated Lean files in {folder}/ (Kummer-Dedekind where p is coprime to d = {d})")
