###############################################################################
#  RingOfIntegersLeanProofWriter.sage
#
#  Updated port of the two scripts of the predecessor project
#  (github.com/alainchmt/RingOfIntegersProject):
#      IrreducibilityLeanProofWriter.sage
#      RingOfIntegersLeanProofWriter.sage
#
#  Given a monic irreducible T in ZZ[x], an integral basis and an index, it
#  writes exactly two Lean files, as the original pair did:
#
#      Irreducible{i}.lean   an irreducibility certificate for T
#      NF_{i}.lean           a proof that `O` is the ring of integers of
#                            `K = AdjoinRoot (map (algebraMap ZZ QQ) T)`,
#                            together with `T_discr` and `K_discr`
#
#  * Imports point at `IdealArithmetic.DedekindProject.*`.
#
#  Entry point:
#      generate_ring_of_integers_lean(T, B, index, label=..., out_dir=...,
#                                     lean_root=..., native=False)
#
#  `native=True` reproduces the `*NativeDecide` variants of the old repo:
#  the heavy obligations become `native_decide`, while `timesTableT_eq_Table`
#  and `root_in_subalgebra_lists` stay kernel-checked, exactly as there.
#
#  Usage:
#      load('RingOfIntegersLeanProofWriter.sage')
#      R.<x> = PolynomialRing(ZZ)
#      Kx.<a> = PolynomialRing(QQ)
#      generate_ring_of_integers_lean(x^3 - 3*x - 10, [1, a, (a^2 - a)/2], 0,
#                                     label='3.1.648.1',
#                                     out_dir='IdealArithmetic/DedekindProject/Degree3Examples',
#                                     lean_root='IdealArithmetic.DedekindProject.Degree3Examples')
#
#  Updated with the help of Claude Code (Opus 5).
###############################################################################

from itertools import combinations
import itertools
import os
import re

from functools import lru_cache

from sage.rings.number_field.number_field_base import NumberField as NumberField_base

load('IrreducibilityLeanProofWriter.sage')

# Lean module prefix under which the generated files sit; the ring-of-integers
# file imports `{LEAN_ROOT}.Irreducible{i}`.  Overridden per call.
LEAN_ROOT = 'IdealArithmetic.DedekindProject.Degree3Examples'


def BasisToMatrix(B):
    n = len(B)
    d = 1
    L = [i.list() + (n - len(i.list())) * [0] for i in B]
    M = matrix(L).transpose()
    for i in range(n):
        for j in range(n):
            d = lcm(d, denominator(M[i,j]))
    return d * M, d


def SubalgebraBuilderF(T, C, d):
    """Builds a term of type SubalgebraBuilderLists in Lean.
    Returns (str, A, auxTemp) where A is the times table and auxTemp is C^{-1} * (d * e_1)."""
    n = T.degree()
    K.<a> = NumberField(T)
    S.<X> = PolynomialRing(ZZ)
    T_S = S(T.coefficients(sparse=False))
    MM = (1/d) * C
    MMinv = MM.inverse()
    A = [[[] for j in range(n)] for i in range(n)]
    for i in range(n):
        for j in range(n):
            A[i][j] = (MMinv * matrix([(K(MM.column(i)) * K(MM.column(j))).list()]).transpose()).transpose().list()

    s = [[-S(C.column(i).list()) * S(C.column(j).list()) // T_S for j in range(n)] for i in range(n)]
    B = [S(C.column(i).list()) for i in range(n)]
    s = [[s[i][j].list() for j in range(n)] for i in range(n)]

    out = f"noncomputable def BQ : SubalgebraBuilderLists {n} ℤ  ℚ K T l where\n"
    out += f" d := {d}\n"
    out += " hlen := rfl\n"
    out += " htr := rfl\n"
    out += " hofL := T_ofList.symm\n"
    out += " hm := rfl\n"
    out += " B := !["
    items = ['!' + str(B[i].list() + [0] * (n - len(B[i].list()))) for i in range(n)]
    out += ", ".join(items[:-1])
    if len(items) > 1:
        out += ", "
    out += items[-1] + "]\n"

    stra = " "
    for i in range(n):
        stra += "!["
        for j in range(n):
            if j != n - 1:
                stra += '!' + str(A[i][j]) + ','
            else:
                stra += '!' + str(A[i][j])
        if i != n - 1:
            stra += '], \n'
        else:
            stra += ']'
    stra += "]"
    out += " a := ![" + stra + "\n"

    strs = ""
    for i in range(n):
        if i != n - 1:
            strs += '!' + str(s[i]) + ','
        else:
            strs += '!' + str(s[i])
    strs += "]"
    out += " s := ![" + strs + "\n"
    out += """ h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide \n"""
    return out, A, C.inverse() * (d * vector([0 if i != 1 else 1 for i in range(n)]))


def CertificateDedekindCriterionF(T, p):
    """Certificate of Dedekind criterion for T at prime p.
    Returns a Lean string if T satisfies the criterion at p, or None otherwise."""
    S.<X> = PolynomialRing(ZZ)
    R.<x> = PolynomialRing(GF(p))
    T_coeffs = T.coefficients(sparse=False)
    T_S = S(T_coeffs)
    T_R = R(T_coeffs)
    g = radical(T_R)
    F = T_R.factor()
    kl = len(F)
    n = max([F[i][1] for i in range(kl)])
    t, ap, bp = xgcd(g, derivative(g))
    k = R((g^n) / T_R)
    h = S(R(T_R / g))
    f = (S(g) * h - T_S) / p
    gcd, at, bt = xgcd(R(f), g)
    gcd2, at2, c = xgcd(gcd, R(h))
    a = at2 * at
    b = at2 * bt
    c = c

    if gcd2 == 1:
        out = f"def CD{p}: CertificateDedekindCriterionLists l {p} where\n"
        out += f" n := {n}\n"
        out += f" a' := {ap.list()}\n"
        out += f" b' := {bp.list()}\n"
        out += f" k := {k.list()}\n"
        out += f" f := {f.list()}\n"
        out += f" g := {g.list()}\n"
        out += f" h := {h.list()}\n"
        out += f" a := {a.list()}\n"
        out += f" b := {b.list()}\n"
        out += f" c := {c.list()}\n"
        out += " hdvdpow := rfl\n"
        out += " hcop := rfl\n"
        out += " hf := by rfl\n"
        out += " habc := by rfl\n\n"
        return out
    return None


def CertificateDedekindF(T):
    """Certificate proving T satisfies Dedekind criterion at all primes except those in 'bad'.
    Returns (str, bad) where str is the Lean code and bad is the list of exceptional primes."""
    D, a, b = xgcd(T, derivative(T))
    if D < 0:
        a = -a
        b = -b
    F = factor(D)
    n = len(F)
    pl = [t[0] for t in F]
    exp = [t[1] for t in F]

    out = ""
    for p in set(pl):
        out += f"instance hp{p}: Fact $ Nat.Prime {p} := fact_iff.2 (by norm_num)\n"
    out += "\n"

    good = []
    for p in pl:
        cert = CertificateDedekindCriterionF(T, p)
        if cert is not None:
            out += cert
            good.append(p)

    bad = list(set(pl) - set(good))

    out += f"noncomputable def D : CertificateDedekindAlmostAllLists T l {bad} where\n"
    out += f" n := {len(pl)}\n"
    out += f" p := !{pl}\n"
    out += f" exp := !{exp}\n"
    out += f" pdgood := {good}\n"
    out += " hsub := by decide\n"
    out += " hp := by\n"
    out += "  intro i ; fin_cases i\n"
    for p in pl:
        out += f"  exact hp{p}.out\n"
    out += f" a := {a.list()}\n"
    out += f" b := {b.list()}\n"
    out += " hab := by decide\n"
    out += " hd := by \n"
    out += "  intro p hp \n"
    out += "  fin_cases hp\n"
    for p in good:
        out += f"  exact satisfiesDedekindCriterion_of_certificate_lists T l {p} T_ofList CD{p}\n"
    out += "\n"
    return out, bad


def CertificatePMaximalityF(T, C, denom, p, Table):
    """Certificate of p-maximality for the order with basis encoded in C/denom.
    Returns (str, flag, flagW) where flag=1 means unramified case, flagW=1 means witness found."""
    d = T.degree()
    t = 0
    while p^t < d:
        t = t + 1
    K.<a> = NumberField(T)
    O = K.maximal_order()

    M = (1/denom) * C
    B = [K(M.column(i).list()) for i in range(d)]

    MFrob = matrix([(i^(p^t)).list() for i in B]).transpose()
    Coeff = M.inverse() * MFrob
    MS = MatrixSpace(GF(p), d)
    CoeffMod = MS(Coeff)

    m = CoeffMod.right_nullity()
    n = d - m

    v = CoeffMod.right_kernel().matrix().rows()
    v_ind = CoeffMod.right_kernel().matrix().pivots()
    w_ind = CoeffMod.transpose().echelon_form().pivots()
    X = CoeffMod.solve_right(CoeffMod.transpose().echelon_form().transpose())
    wFrob = [CoeffMod.transpose().echelon_form().transpose().column(i) for i in range(n)]
    w = [X.column(i) for i in range(n)]

    flag = 0
    flagW = 0
    out = ""

    if m == 0:
        flag = 1
        out += f"noncomputable def M{p} : MaximalOrderCertificateOfUnramifiedLists {p} O Om hm where\n"
        out += f" n := {n}\n"
        out += f" t := {t}\n"
        out += " hpos := by decide\n"
        out += " TT := timesTableO\n"
        out += " B' := B'\n"
        out += " T := Table\n"
        out += " heq := timesTableT_eq_Table\n"
        strT = ""
        for i in range(d):
            if i != d - 1:
                strT += '!' + str([[GF(p)(Table[i][j][k]) for k in range(d)] for j in range(d)]) + ', \n'
            else:
                strT += '!' + str([[GF(p)(Table[i][j][k]) for k in range(d)] for j in range(d)])
        out += " TMod := ![" + strT + "]\n"
        out += " hTMod := by decide\n"
        out += " hle := by decide\n"
        strw = ""
        for i in range(n):
            if i != n - 1:
                strw += '!' + str(w[i].list()) + ','
            else:
                strw += '!' + str(w[i].list())
        out += " w := ![" + strw + "]\n"
        strF = ""
        for i in range(n):
            if i != n - 1:
                strF += '!' + str(wFrob[i].list()) + ','
            else:
                strF += '!' + str(wFrob[i].list())
        out += " wFrob := ![" + strF + "]\n"
        out += " w_ind := !" + str([w_ind[i] for i in range(n)]) + "\n"
        out += """ hindw := by decide
 hwFrobComp := by decide \n"""
    else:
        MQQ = MatrixSpace(ZZ, d)
        MQ1 = MatrixSpace(ZZ, m, d)
        MQ2 = MatrixSpace(ZZ, n, d)
        if m > 0:
            Brad = MQ1(matrix(v)).transpose().augment(p * MQ2(matrix(w)).transpose())
        else:
            Brad = p * MQ2(matrix(w)).transpose()
        Brad2 = M * Brad

        ListBasisRad = [K(Brad2.column(i)) for i in range(d)]

        def MatrixEndoMul(j):
            return MS(Brad2.inverse() * matrix([(B[j] * ListBasisRad[i]).list() for i in range(d)]).transpose())

        set_random_seed(12345)

        for i in range(100):
            W = random_vector(ZZ, d, floor(d/2))
            LII = matrix([(MatrixEndoMul(i) * W).list() for i in range(d)]).transpose()
            if not LII.is_singular():
                flagW = 1
                break

        if flagW == 1:
            LII = matrix([(MatrixEndoMul(i) * W).list() for i in range(d)]).transpose()
            Wit = K((Brad2 * W).list())
            G = LII.inverse()
            g = [[ZZ(G[i][j]) for i in range(d)] for j in range(d)]

            def Endo(j):
                return Brad2.inverse() * vector(((K((M * matrix(g[j]).transpose()).list())) * Wit).list())

            for j in range(d):
                denom_j = LCM([(Endo(j)[k]).denominator() for k in range(d)])
                g[j] = [denom_j * g[j][i] for i in range(d)]

            def a_aux(i):
                return [Endo(i)[k] for k in range(m)]
            def c_aux(i):
                return [Endo(i)[m + k] for k in range(n)]

            a = [a_aux(i) for i in range(d)]
            c = [c_aux(i) for i in range(d)]

            def ac_ind_aux(i):
                if i < m:
                    return 'Sum.inl ' + str(i)
                else:
                    return 'Sum.inr ' + str(i - m)
        else:
            MM = matrix([(MatrixEndoMul(j)).list() for j in range(d)])
            ab_aux = MM.echelon_form().pivots()
            gm = MQQ((MM.transpose().solve_right(MM.echelon_form().transpose()))).columns()
            g = [[gm[j][i] for i in range(d)] for j in range(d)]

            def Endo(j):
                return Brad2.inverse() * (matrix([((K((M * matrix(g[j]).transpose()).list())) * ListBasisRad[i]).list() for i in range(d)]).transpose())

            for j in range(d):
                denom_j = LCM([LCM([(Endo(j)[i][k]).denominator() for k in range(d)]) for i in range(d)])
                g[j] = [denom_j * g[j][i] for i in range(d)]

            def a_aux(i, j):
                return [Endo(i).column(j)[k] for k in range(m)]
            def c_aux(i, j):
                return [Endo(i).column(j)[m + k] for k in range(n)]

            a = [[a_aux(i, j) for j in range(m)] for i in range(d)]
            c = [[c_aux(i, j) for j in range(m)] for i in range(d)]
            dl = [[a_aux(i, m + j) for j in range(n)] for i in range(d)]
            e = [[c_aux(i, m + j) for j in range(n)] for i in range(d)]

            def index_adjust(i, m, n):
                dd = m + n
                r = i % dd
                s = floor(i / dd)
                col = ('Sum.inl ' + str(r)) if r < m else ('Sum.inr ' + str(r - m))
                row = ('Sum.inl ' + str(s)) if s < m else ('Sum.inr ' + str(s - m))
                return (col, row)

            ab_ind = [index_adjust(i, m, n) for i in ab_aux]

        if flagW == 1:
            out += f"noncomputable def M{p} : MaximalOrderCertificateWLists {p} O Om hm where\n"
        else:
            out += f"noncomputable def M{p} : MaximalOrderCertificateLists {p} O Om hm where\n"
        out += f" m := {m}\n"
        out += f" n := {n}\n"
        out += f" t := {t}\n"
        out += " hpos := by decide\n"
        out += " TT := timesTableO\n"
        out += " B' := B'\n"
        out += " T := Table\n"
        out += " heq := timesTableT_eq_Table\n"
        strT = ""
        for i in range(d):
            if i != d - 1:
                strT += '!' + str([[GF(p)(Table[i][j][k]) for k in range(d)] for j in range(d)]) + ', \n'
            else:
                strT += '!' + str([[GF(p)(Table[i][j][k]) for k in range(d)] for j in range(d)])
        out += " TMod := ![" + strT + "]\n"
        out += " hTMod := by decide\n"
        out += " hle := by decide\n"
        strv = ""
        for i in range(m):
            if i != m - 1:
                strv += '!' + str(v[i].list()) + ','
            else:
                strv += '!' + str(v[i].list())
        out += " b1 := ![" + strv + "]\n"
        strw = ""
        for i in range(n):
            if i != n - 1:
                strw += '!' + str(w[i].list()) + ','
            else:
                strw += '!' + str(w[i].list())
        out += " b2 := ![" + strw + "]\n"
        out += " v := ![" + strv + "]\n"
        out += " w := ![" + strw + "]\n"
        strF = ""
        for i in range(n):
            if i != n - 1:
                strF += '!' + str(wFrob[i].list()) + ','
            else:
                strF += '!' + str(wFrob[i].list())
        out += " wFrob := ![" + strF + "]\n"
        out += " v_ind := !" + str([v_ind[i] for i in range(m)]) + "\n"
        out += " w_ind := !" + str([w_ind[i] for i in range(n)]) + "\n"
        out += """ hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide \n"""
        strg = ""
        for i in range(d):
            if i != d - 1:
                strg += '!' + str(g[i]) + ','
            else:
                strg += '!' + str(g[i])
        out += " g := ![" + strg + "]\n"

        if flagW == 1:
            out += " w1 := !" + str([W[i] for i in range(m)]) + "\n"
            out += " w2 := !" + str([W[m + i] for i in range(n)]) + "\n"
            stra = ""
            for i in range(d):
                if i != d - 1:
                    stra += '!' + str(a[i]) + ','
                else:
                    stra += '!' + str(a[i])
            out += " a := ![" + stra + "]\n"
            strc = ""
            for i in range(d):
                if i != d - 1:
                    strc += '!' + str(c[i]) + ','
                else:
                    strc += '!' + str(c[i])
            out += " c := ![" + strc + "]\n"
            out += " hmulw := by decide \n"
            strac_indw = ""
            for i in range(d):
                if i != d - 1:
                    strac_indw += ac_ind_aux(i) + ', '
                else:
                    strac_indw += ac_ind_aux(i)
            out += " ac_indw := ![" + strac_indw + "]\n"
            out += " hacindw := by decide \n\n"
        else:
            stra = ""
            for i in range(d):
                stra += '!['
                for j in range(m):
                    if j != m - 1:
                        stra += '!' + str(a[i][j]) + ','
                    else:
                        stra += '!' + str(a[i][j])
                if i != d - 1:
                    stra += '],'
                else:
                    stra += ']'
            out += " a := ![" + stra + "]\n"

            strc = ""
            for i in range(d):
                strc += '!['
                for j in range(m):
                    if j != m - 1:
                        strc += '!' + str(c[i][j]) + ','
                    else:
                        strc += '!' + str(c[i][j])
                if i != d - 1:
                    strc += '],'
                else:
                    strc += ']'
            out += " c := ![" + strc + "]\n"

            strd = ""
            for i in range(d):
                strd += '!['
                for j in range(n):
                    if j != n - 1:
                        strd += '!' + str(dl[i][j]) + ','
                    else:
                        strd += '!' + str(dl[i][j])
                if i != d - 1:
                    strd += '],'
                else:
                    strd += ']'
            out += " d := ![" + strd + "]\n"

            stre = ""
            for i in range(d):
                stre += '!['
                for j in range(n):
                    if j != n - 1:
                        stre += '!' + str(e[i][j]) + ','
                    else:
                        stre += '!' + str(e[i][j])
                if i != d - 1:
                    stre += '],'
                else:
                    stre += ']'
            out += " e := ![" + stre + "]\n"

            strind = ""
            for i in range(d):
                if i != d - 1:
                    strind += '(' + ab_ind[i][0] + ', ' + ab_ind[i][1] + '),'
                else:
                    strind += '(' + ab_ind[i][0] + ', ' + ab_ind[i][1] + ')'
            out += " ab_ind := ![" + strind + "]\n"
            out += """ hindab := by decide
 hmul1 := by decide
 hmul2 := by decide
            \n"""
    return out, flag, flagW


def LeanProofRingOfIntegers(T, basis, nameIrr, comment, lean_root, with_discr=True,
                            native=False):
    """Builds the Lean proof that `O` is the ring of integers of `K`.

    Adapted from `LeanProof` in InvariantsNFLean.sage.  The differences:
    `K` is a `local notation` rather than a `def` (so instance search sees
    through to `AdjoinRoot` and no `CommRing`/`Algebra`/`IsScalarTower`
    scaffolding is needed); the class-group-only trailer is dropped; and the
    `O_ringOfIntegers` conclusion plus the discriminant are appended.

    Returns (str, bad)."""
    d = T.degree()
    T_lean = str(T).replace('x', 'X')
    C, denom = BasisToMatrix(basis)

    out = f"""
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import {lean_root}.{nameIrr}"""
    if with_discr:
        # `…DedekindProject.Discriminant` already pulls in
        # `Mathlib.NumberTheory.NumberField.Discriminant.Basic`, which is where
        # `NumberField.discr` now lives (the old monolithic
        # `Mathlib.NumberTheory.NumberField.Discriminant` has been split up).
        out += """
import IdealArithmetic.DedekindProject.Discriminant"""
    out += f"""

{comment}

open Polynomial Module

noncomputable def T : ℤ[X] := {T_lean}
lemma T_def : T = {T_lean} := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

noncomputable instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

local notation "l" => {T.list()}

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
"""
    out += f"-- We build the subalgebra with integral basis {basis} \n\n"

    sub_out, Table, auxTemp = SubalgebraBuilderF(T, C, denom)
    out += sub_out

    out += f"""
lemma T_degree : T.natDegree = {d} := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

theorem hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin {d}) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin {d}) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ

noncomputable def B : Basis (Fin {d}) ℤ O := timesTableO.basis
"""
    strTa = ""
    out += f"def Table : Fin {d} → Fin {d} → List ℤ := \n !["
    for i in range(d):
        if i != d - 1:
            strTa = strTa + ' !' + str(Table[i]) + ', \n'
        else:
            strTa = strTa + ' !' + str(Table[i])
    out += strTa + "]\n"

    out += f"""
lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ !{auxTemp.list()} [] (by decide)
"""
    ded_out, bad = CertificateDedekindF(T)
    out += ded_out

    flagl = []
    flaglW = []
    for p in bad:
        pmax_out, flagp, flagW = CertificatePMaximalityF(T, C, denom, p, Table)
        out += pmax_out
        flagl = flagl + [(p, flagp)]
        flaglW = flaglW + [(p, flagW)]
    flagl = dict(flagl)
    flaglW = dict(flaglW)

    # `K` is opaque, so the `Field`/`NumberField` structure has to be handed
    # over explicitly rather than found through `AdjoinRoot`.
    out += f"""
instance hirr : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
 out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

noncomputable instance K_field : Field K := by
  unfold K
  exact AdjoinRoot.instField

instance K_numberField : NumberField K := by
  unfold K
  exact AdjoinRoot.instNumberFieldRat

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ {bad}
  · fin_cases hc
"""
    for p in bad:
        if flagl[p] == 0:
            if flaglW[p] == 1:
                out += f'    exact @pMaximal_of_MaximalOrderCertificateWLists K {p} _ HasUniqueDiv.to_noZeroSMulDivisors_int _ O Om hm _ _ M{p}\n'
            else:
                out += f'    exact @pMaximal_of_MaximalOrderCertificateLists K {p} _ HasUniqueDiv.to_noZeroSMulDivisors_int _ O Om hm _ _ M{p}\n'
        else:
            out += f'    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K {p} _ HasUniqueDiv.to_noZeroSMulDivisors_int _ O Om hm _ _ M{p}\n'

    out += f"""  · have : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T _ T_ofList {bad} D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl
"""

    if with_discr:
        D = NumberField(T, 'a').discriminant()
        lT = T.list()
        dl = [(i + 1) * lT[i + 1] for i in range(len(lT) - 1)] + [0]
        tac = 'native_decide' if native else 'decide +kernel'
        out += f"""
lemma T_discr : T.discr = {T.discriminant()} :=  by
  rw [Monic.discr_def T T_monic, T_degree, ← T_ofList]
  have : {list(lT)}.derivative = {dl} := rfl
  rw [← ofList_derivative_eq_derivative , this]
  {tac}

theorem K_discr : NumberField.discr K = {D} := by
  rw [discr_numberField_eq_discrSubalgebraBuilder T_irreducible BQ O_ringOfIntegers]
  rw [T_discr]
  rfl
"""
    return out, bad


def generate_ring_of_integers_lean(T, B, index, label=None, out_dir='.',
                                   lean_root=None, native=False, with_discr=True):
    """Write `Irreducible{index}.lean` and `NF_{index}.lean` into `out_dir`.

    T     : monic irreducible polynomial in ZZ['x']
    B     : integral basis, as elements of QQ[a] or of a number field
    index : the integer naming both files, as in the predecessor project
    label : LMFDB label, placed in a comment at the top of the NF_ file
    native: emit `native_decide` for the heavy obligations
    """
    global LEAN_ROOT
    if lean_root is not None:
        LEAN_ROOT = lean_root
    lean_root = LEAN_ROOT

    T = ZZ['x'](T)
    # Pull the basis into a common parent.  A literal `1` in the basis is a
    # Sage `Integer`, whose `.list()` is `[1]` rather than the length-n
    # coefficient vector `BasisToMatrix` expects.
    B = list(Sequence(B))

    os.makedirs(out_dir, exist_ok=True)
    nameIrr = f'Irreducible{index}'
    comment = f'-- Number field with label {label} in the LMFDB' if label else ''

    irr_str = _retactic(LeanProofIrreducible(T), native)
    with open(os.path.join(out_dir, f'{nameIrr}.lean'), 'w') as fh:
        fh.write(irr_str)

    roi_str, bad = LeanProofRingOfIntegers(T, B, nameIrr, comment, lean_root,
                                           with_discr=with_discr, native=native)
    roi_str = _retactic(roi_str, native)
    with open(os.path.join(out_dir, f'NF_{index}.lean'), 'w') as fh:
        fh.write(roi_str)

    if 'sorry' in irr_str or 'sorry' in roi_str:
        print(f'  WARNING: `sorry` emitted for index {index} ({label})')
    print(f'Generated Irreducible{index}.lean and NF_{index}.lean in {out_dir}/'
          + ('  [native_decide]' if native else ''))
    return bad


# The example batches of the predecessor project.  Each row is
# (LMFDB label or None, coefficient list of T in ascending order, integral
# basis), where the basis is either a callable taking the generator or a string
# in the generator `a`.
DEGREE3_EXAMPLES = [
    ('3.1.648.1',   [-10, -3, 0, 1], lambda a: [1, a, (a**2 - a) / 2]),
    ('3.1.2700.1',  [-20, 0, 0, 1],  lambda a: [1, a, a**2 / 2]),
    ('3.1.6075.1',  [-45, 0, 0, 1],  lambda a: [1, a, a**2 / 3]),
    ('3.1.9720.1',  [-18, 27, 0, 1], lambda a: [1, a, a**2 / 3]),
    ('3.1.9720.2',  [-48, -18, 0, 1], lambda a: [1, a, a**2 / 2]),
    ('3.1.9720.3',  [-24, 18, 0, 1], lambda a: [1, a, a**2 / 2]),
    ('3.1.16200.2', [-80, -30, 0, 1], lambda a: [1, a, a**2 / 2]),
]

DEGREE5_EXAMPLES = [
    ('5.1.250000.1', [-4, 10, 0, -5, 0, 1], '[1, a, a^2, a^3, 1/2*a^4 - 1/2*a^2]'),
    ('5.5.390625.1', [-1, 10, -5, -10, 0, 1], '[1, a, a^2, a^3, 1/7*a^4 - 3/7*a^3 - 1/7*a^2 - 2/7*a + 2/7]'),
    ('5.1.1000000.1', [-12, -5, 0, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/4*a^4 - 1/4*a^3 + 1/4*a^2 - 1/4*a]'),
    ('5.1.1012500.1', [-12, 0, 0, -5, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/2*a^4 - 1/2*a^2]'),
    ('5.1.2700000.1', [20, 30, -10, -5, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/24*a^4 - 5/24*a^3 - 1/6*a^2 + 5/12*a + 1/6]'),
    ('5.1.3515625.1', [-12, 10, -15, 10, 0, 1], '[1, a, a^2, a^3, 1/22*a^4 + 2/11*a^3 + 2/11*a^2 + 1/22*a - 4/11]'),
    ('5.1.6250000.1', [-18, -15, -10, 10, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/24*a^4 - 1/8*a^3 - 5/24*a^2 + 5/24*a - 1/4]'),
    ('5.1.7500000.1', [-16, -20, 0, 5, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/4*a^4 + 1/4*a^2]'),
    ('5.1.7812500.1', [-10, 25, 0, 0, 0, 1], '[1, a, a^2, a^3, 1/18*a^4 + 5/18*a^3 + 7/18*a^2 - 1/18*a + 1/9]'),
    ('5.3.8100000.3', [-36, -45, 0, 0, 0, 1], '[1, a, a^2, 1/6*a^3 - 1/2*a, 1/12*a^4 - 1/12*a^3 - 1/4*a^2 + 1/4*a]'),
    ('5.1.8100000.3', [6, 15, -10, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/4*a^4 - 1/4*a^3 - 1/4*a^2 - 1/4*a - 1/2]'),
    ('5.1.9000000.1', [-96, 40, 0, 10, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/24*a^4 - 1/12*a^3 + 1/12*a^2 - 1/6*a]'),
    ('5.1.13500000.3', [80, 0, -10, -5, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/28*a^4 - 1/7*a^3 + 11/28*a^2 + 1/14*a - 2/7]'),
    ('5.1.15000000.1', [108, 45, -20, -10, 0, 1], '[1, a, a^2, 1/4*a^3 - 1/2*a^2 - 1/4*a, 1/12*a^4 - 1/12*a^2 - 1/6*a]'),
    ('5.1.16200000.1', [-96, -45, -20, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/48*a^4 + 5/48*a^3 - 23/48*a^2 + 3/16*a]'),
    ('5.1.24300000.2', [-42, 15, -10, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/12*a^4 + 1/12*a^3 - 5/12*a^2 - 1/4*a - 1/2]'),
    ('5.1.24300000.4', [-16, 0, -10, -5, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/4*a^4 - 1/4*a^2 - 1/2*a]'),
    ('5.1.25000000.1', [88, -15, -40, 10, 0, 1], '[1, a, a^2, 1/4*a^3 - 1/2*a^2 - 1/4*a, 1/28*a^4 + 3/28*a^3 + 5/28*a^2 + 3/28*a + 2/7]'),
    ('5.1.25312500.1', [-252, -135, -30, 0, 0, 1], '[1, a, a^2, 1/3*a^3, 1/246*a^4 - 3/82*a^3 + 27/82*a^2 - 7/82*a + 9/41]'),
    ('5.1.25312500.2', [78, 15, -30, 0, 0, 1], '[1, a, 1/2*a^2 - 1/2*a, 1/4*a^3 + 1/4*a - 1/2, 1/8*a^4 - 1/8*a^3 + 1/8*a^2 + 1/8*a - 1/4]'),
    ('5.1.27000000.1', [64, 0, -10, 5, 0, 1], '[1, a, 1/2*a^2 - 1/2*a, 1/4*a^3 - 1/4*a^2 - 1/2*a, 1/8*a^4 + 1/8*a^2 + 1/4*a]'),
    ('5.3.40500000.1', [284, 135, -40, -20, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/96*a^4 + 7/96*a^3 + 29/96*a^2 - 29/96*a + 7/24]'),
    ('5.1.40500000.1', [-300, 75, 0, 0, 0, 1], '[1, a, a^2, 1/10*a^3 - 1/2*a, 1/80*a^4 - 3/80*a^3 + 5/16*a^2 + 1/16*a - 1/4]'),
    ('5.3.42187500.1', [236, -15, -20, -10, 0, 1], '[1, a, 1/2*a^2 - 1/2*a, 1/4*a^3 - 1/4*a, 1/16*a^4 + 1/16*a^3 - 1/16*a^2 - 5/16*a + 1/4]'),
    ('5.1.42187500.1', [-58, -15, -10, 10, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/24*a^4 - 5/24*a^3 + 11/24*a^2 + 7/24*a - 1/12]'),
    ('5.1.48600000.1', [-96, 0, -30, 5, 0, 1], '[1, a, 1/2*a^2 - 1/2*a, 1/2*a^3 - 1/2*a, 1/16*a^4 - 1/4*a^3 - 3/16*a^2 + 3/8*a - 1/2]'),
    ('5.1.48600000.3', [-12, -30, -10, 15, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/6*a^4 + 1/6*a^3 - 1/3*a^2]'),
    ('5.1.48600000.4', [-12, 30, -10, -15, 0, 1], '[1, a, a^2, a^3, 1/2*a^4 - 1/2*a^2]'),
    ('5.1.48600000.5', [64, 120, -40, -10, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/24*a^4 - 1/12*a^3 - 1/4*a^2 - 1/6*a + 1/3]'),
    ('5.3.67500000.1', [18, 15, -30, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/12*a^4 - 1/4*a^3 + 1/4*a^2 - 1/4*a - 1/2]'),
    ('5.1.67500000.1', [-26, -45, -50, -20, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/4*a^4 - 1/4*a^3 - 1/4*a^2 - 1/4*a - 1/2]'),
    ('5.1.67500000.3', [54, 15, -10, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/12*a^4 - 1/4*a^3 + 1/4*a^2 + 5/12*a - 1/2]'),
    ('5.1.72900000.2', [-24, -30, -20, 15, 0, 1], '[1, a, a^2, a^3, 1/58*a^4 + 3/29*a^3 - 7/58*a^2 - 2/29*a + 2/29]'),
    ('5.1.75000000.1', [198, 135, -40, -15, 0, 1], '[1, a, a^2, 1/3*a^3 + 1/3*a^2 + 1/3*a, 1/69*a^4 - 3/23*a^3 - 1/23*a^2 - 13/69*a - 8/23]'),
    ('5.1.75937500.3', [-36, -30, -40, -15, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/18*a^4 + 1/6*a^3 - 1/3*a^2 - 2/9*a - 1/3]'),
    ('5.3.81000000.2', [-12, -30, -30, -15, 0, 1], '[1, a, a^2, a^3, 1/2*a^4 - 1/2*a^2]'),
    ('5.3.112500000.1', [-544, -240, -20, -10, 0, 1], '[1, a, 1/2*a^2, 1/12*a^3 - 1/6*a^2 + 1/6*a - 1/3, 1/24*a^4 - 1/12*a^2 - 1/2*a - 1/3]'),
    ('5.3.121500000.4', [270, 225, -10, -30, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/24*a^4 + 1/8*a^3 + 1/8*a^2 - 1/24*a + 1/4]'),
    ('5.1.121500000.1', [-72, 75, -20, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/12*a^4 - 1/4*a^3 - 1/4*a^2 + 1/12*a]'),
    ('5.1.121500000.2', [-54, 135, -30, 0, 0, 1], '[1, a, a^2, 1/6*a^3 - 1/2*a, 1/36*a^4 - 1/12*a^3 - 1/4*a^2 - 1/12*a - 1/2]'),
    ('5.3.125000000.1', [-160, -100, 0, 0, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/8*a^4 - 1/4*a^2]'),
    ('5.3.125000000.3', [160, 0, -50, -25, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/152*a^4 - 2/19*a^3 - 73/152*a^2 + 27/76*a + 6/19]'),
    ('5.1.135000000.2', [-52, 45, -20, -10, 0, 1], '[1, a, a^2, 1/4*a^3 - 1/2*a^2 - 1/4*a, 1/12*a^4 - 1/12*a^3 - 1/4*a^2 - 5/12*a - 1/3]'),
    ('5.1.145800000.1', [-288, 0, -30, 15, 0, 1], '[1, a, a^2, 1/6*a^3 - 1/2*a, 1/24*a^4 - 3/8*a^2 - 1/4*a]'),
    ('5.1.145800000.5', [48, 60, -40, 0, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/8*a^4 - 1/4*a^2]'),
    ('5.1.158203125.7', [-600, 0, 0, -25, 0, 1], '[1, a, 1/2*a^2 - 1/2*a, 1/10*a^3 - 1/2*a, 1/20*a^4 - 1/4*a^2]'),
    ('5.3.202500000.1', [-144, -30, -10, -15, 0, 1], '[1, a, a^2, 1/3*a^3 + 1/3*a^2 + 1/3*a, 1/18*a^4 - 1/2*a^2 - 2/9*a - 1/3]'),
    ('5.3.202500000.3', [96, 120, -60, -15, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/184*a^4 - 4/23*a^3 + 89/184*a^2 + 9/46*a + 9/23]'),
    ('5.1.202500000.1', [-80, 150, -50, -5, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/8*a^4 + 1/8*a^3 + 1/4*a]'),
    ('5.1.225000000.2', [-24, 60, -70, 15, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/24*a^4 - 1/12*a^3 - 5/24*a^2 - 1/2*a - 1/2]'),
    ('5.1.227812500.1', [-48, 240, -20, 0, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3, 1/112*a^4 + 5/56*a^3 - 3/28*a^2 - 1/4*a - 5/14]'),
    ('5.1.281250000.1', [-300, 250, 0, -25, 0, 1], '[1, a, a^2, 1/5*a^3, 1/10*a^4 - 1/2*a^2]'),
    ('5.3.303750000.1', [-24, -180, -10, -15, 0, 1], '[1, a, 1/4*a^2 - 1/4*a - 1/2, 1/4*a^3 + 1/4*a - 1/2, 1/32*a^4 + 1/16*a^3 - 3/32*a^2 - 1/4*a - 1/8]'),
    ('5.1.337500000.1', [-216, 60, -30, 15, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/24*a^4 - 1/4*a^3 + 1/8*a^2 - 1/2]'),
    ('5.1.337500000.4', [432, 210, -10, -15, 0, 1], '[1, a, a^2, 1/7*a^3 - 2/7*a^2 + 1/7*a - 1/7, 1/42*a^4 - 1/14*a^2 + 4/21*a + 2/7]'),
    ('5.3.364500000.2', [384, 240, -40, -30, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/16*a^4 + 1/8*a^2 - 1/2*a]'),
    ('5.1.364500000.3', [24, 60, -20, 0, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/4*a^4]'),
    ('5.3.379687500.1', [-8, -15, -10, -40, 0, 1], '[1, a, a^2, a^3, 1/42*a^4 - 17/42*a^3 - 1/14*a^2 - 1/42*a + 1/21]'),
    ('5.3.379687500.2', [492, -240, -10, -15, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/796*a^4 - 67/796*a^3 + 24/199*a^2 + 81/199*a + 85/199]'),
    ('5.3.405000000.1', [-4, 30, -50, 5, 0, 1], '[1, a, a^2, a^3, 1/6*a^4 + 1/3*a^3 - 1/2*a^2 - 1/3*a + 1/3]'),
    ('5.1.405000000.1', [-480, 0, -50, 15, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/8*a^4 - 1/8*a^2 - 1/4*a]'),
    ('5.1.405000000.7', [-192, 180, 0, 20, 0, 1], '[1, a, 1/2*a^2, 1/8*a^3 - 1/4*a, 1/16*a^4 - 1/8*a^2 - 1/2*a]'),
    ('5.1.405000000.12', [-96, -120, 0, 30, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/16*a^4 - 1/8*a^3 + 1/8*a^2 - 1/4*a]'),
    ('5.1.421875000.2', [-180, 75, 0, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/48*a^4 - 3/16*a^3 - 5/16*a^2 - 3/16*a + 1/4]'),
    ('5.3.480000000.1', [-96, -20, 0, -20, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/12*a^4 + 1/12*a^3 + 1/6*a^2 + 1/6*a]'),
    ('5.1.480000000.2', [-228, -65, -60, 10, 0, 1], '[1, a, a^2, 1/15*a^3 + 2/5*a^2 + 2/15*a + 1/5, 1/15*a^4 - 4/15*a^2 + 2/5*a - 1/5]'),
    ('5.1.607500000.4', [-120, 150, -100, 15, 0, 1], '[1, a, a^2, 1/3*a^3 - 1/3*a^2, 1/54*a^4 - 1/27*a^3 + 19/54*a^2 + 4/9*a - 1/9]'),
    ('5.1.607500000.5', [-88, 90, -70, 25, 0, 1], '[1, a, a^2, 1/7*a^3 + 3/7*a^2 + 1/7*a + 2/7, 1/14*a^4 - 1/14*a^2 + 3/7*a - 3/7]'),
    ('5.1.632812500.1', [-1200, 0, 0, -25, 0, 1], '[1, a, 1/2*a^2 - 1/2*a, 1/10*a^3 - 1/2*a, 1/140*a^4 + 3/70*a^3 + 5/28*a^2 - 3/7*a + 3/7]'),
    ('5.1.632812500.2', [-270, -225, -50, 0, 0, 1], '[1, a, 1/2*a^2 - 1/2*a, 1/4*a^3 + 1/4*a - 1/2, 1/24*a^4 - 1/8*a^3 - 1/8*a^2 + 7/24*a + 1/4]'),
    ('5.1.632812500.3', [-180, -75, -50, 0, 0, 1], '[1, a, a^2, a^3, 1/18*a^4 - 1/6*a^3 - 1/2*a^2 - 5/18*a - 1/3]'),
    ('5.1.632812500.4', [-150, 0, 0, 25, 0, 1], '[1, a, a^2, 1/5*a^3, 1/40*a^4 + 3/40*a^3 + 1/4*a^2 - 1/4*a + 1/4]'),
    ('5.1.632812500.5', [30, 75, -50, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/4*a^4 - 1/4*a^3 + 1/4*a^2 + 1/4*a - 1/2]'),
    ('5.1.632812500.6', [470, 300, -50, -25, 0, 1], '[1, a, a^2, a^3, 1/438*a^4 - 61/438*a^3 + 32/73*a^2 + 32/219*a - 50/219]'),
    ('5.3.675000000.2', [800, 0, -50, -25, 0, 1], '[1, a, a^2, 1/10*a^3 - 1/2*a, 1/120*a^4 - 1/30*a^3 + 1/8*a^2 + 1/12*a - 1/3]'),
    ('5.1.675000000.1', [-256, -240, -80, -10, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/16*a^4 - 1/8*a^2]'),
    ('5.3.729000000.1', [-600, -525, -100, 0, 0, 1], '[1, a, a^2, 1/10*a^3 - 1/2*a, 1/60*a^4 + 1/60*a^3 + 5/12*a^2 - 1/4*a]'),
    ('5.3.729000000.3', [96, 60, -80, 0, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/24*a^4 + 1/12*a^3 - 1/12*a^2 - 1/2*a]'),
    ('5.3.729000000.4', [156, 510, -10, -45, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/48*a^4 + 7/48*a^3 + 1/12*a^2 + 3/8*a + 1/4]'),
    ('5.1.729000000.1', [-192, 240, -40, -30, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/16*a^4 + 1/8*a^2 - 1/2*a]'),
    ('5.1.729000000.2', [-168, 60, -170, 15, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/888*a^4 + 67/444*a^3 + 211/888*a^2 - 13/37*a - 1/74]'),
    ('5.3.1012500000.1', [-36, -90, -30, 15, 0, 1], '[1, a, a^2, 1/6*a^3 - 1/2*a^2, 1/6*a^4 - 1/2*a^2]'),
    ('5.1.1012500000.1', [-1992, -90, -90, -15, 0, 1], '[1, a, a^2, a^3, 1/9254*a^4 + 1580/4627*a^3 + 519/9254*a^2 + 996/4627*a + 955/4627]'),
    ('5.1.1012500000.2', [-936, -90, -80, 15, 0, 1], '[1, a, a^2, a^3, 1/258*a^4 + 4/43*a^3 + 25/86*a^2 - 1/3*a - 15/43]'),
    ('5.1.1012500000.3', [-648, -540, -210, -15, 0, 1], '[1, a, 1/2*a^2 - 1/2*a, 1/12*a^3 - 1/4*a^2, 1/72*a^4 + 1/24*a^2 + 1/3*a - 1/2]'),
    ('5.3.1125000000.2', [-160, 200, 0, -50, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/16*a^4 - 1/8*a^3 + 1/8*a^2 - 1/4*a]'),
    ('5.3.1125000000.3', [120, 100, -150, -25, 0, 1], '[1, a, a^2, 1/12*a^3 - 5/12*a - 1/2, 1/96*a^4 - 1/48*a^3 + 43/96*a^2 - 11/24*a - 3/8]'),
    ('5.3.1215000000.2', [36, -30, -10, -15, 0, 1], '[1, a, a^2, 1/3*a^3 + 1/3*a^2 + 1/3*a, 1/6*a^4 - 1/2*a^2 + 1/3*a]'),
    ('5.3.1215000000.3', [96, 0, -30, -5, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/8*a^4 + 3/8*a^2 + 1/4*a]'),
    ('5.3.1215000000.5', [528, 120, -170, 15, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/76*a^4 - 3/38*a^3 - 25/76*a^2 - 5/19*a + 3/19]'),
    ('5.1.1215000000.1', [-448, 345, -80, -10, 0, 1], '[1, a, 1/2*a^2 - 1/2*a, 1/4*a^3 - 1/4*a, 1/48*a^4 + 5/48*a^3 - 3/16*a^2 + 19/48*a - 1/3]'),
    ('5.1.1215000000.2', [-396, 270, -90, 35, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/282*a^4 + 7/94*a^3 - 44/141*a^2 + 6/47*a - 17/47]'),
    ('5.1.1423828125.3', [-960, -300, -25, 0, 0, 1], '[1, a, a^2, 1/7*a^3 - 2/7*a^2 + 3/7*a - 1/7, 1/196*a^4 - 2/49*a^3 + 16/49*a^2 + 51/196*a + 19/49]'),
    ('5.3.1518750000.3', [144, -90, -30, 15, 0, 1], '[1, a, a^2, 1/6*a^3 - 1/2*a^2, 1/6*a^4 - 1/2*a^2]'),
    ('5.3.1687500000.3', [-80, 300, -200, 25, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/172*a^4 + 10/43*a^3 + 77/172*a^2 - 11/43*a - 21/43]'),
    ('5.3.1687500000.5', [80, 0, -50, -25, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/12*a^4 + 1/6*a^3 + 1/4*a^2 + 1/3*a - 1/3]'),
    ('5.1.1687500000.2', [-1100, -750, -250, -25, 0, 1], '[1, a, a^2, 1/10*a^3 - 1/2*a^2, 1/120*a^4 - 1/24*a^3 - 1/2*a^2 - 1/12*a + 1/6]'),
    ('5.1.1687500000.3', [-680, -750, -250, -25, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/194*a^4 - 23/97*a^3 - 43/194*a^2 - 9/97*a + 39/97]'),
    ('5.1.1687500000.5', [-80, -150, -100, -25, 0, 1], '[1, a, a^2, a^3, 1/2*a^4 - 1/2*a^2]'),
    ('5.3.1822500000.2', [192, 150, -40, -45, 0, 1], '[1, a, a^2, a^3, 1/158*a^4 - 25/79*a^3 - 73/158*a^2 - 12/79*a - 36/79]'),
    ('5.3.1822500000.3', [228, 150, -10, -45, 0, 1], '[1, a, a^2, 1/6*a^3 - 1/6*a^2, 1/72*a^4 - 5/72*a^3 - 5/18*a^2 + 1/4*a - 1/6]'),
    ('5.1.1822500000.1', [-1152, 0, -60, 30, 0, 1], '[1, a, 1/2*a^2, 1/12*a^3 - 1/2*a, 1/48*a^4 + 1/8*a^2 - 1/4*a]'),
    ('5.1.1822500000.2', [-732, -30, -70, 15, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/8*a^4 + 1/8*a^3 - 1/2*a^2 + 1/4*a - 1/2]'),
    ('5.3.2025000000.1', [-12, -90, -90, -15, 0, 1], '[1, a, a^2, a^3, 1/34*a^4 - 2/17*a^3 + 1/34*a^2 + 4/17*a + 7/17]'),
    ('5.3.2025000000.3', [816, 135, -20, -60, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/2172*a^4 - 307/2172*a^3 + 793/2172*a^2 - 69/724*a + 58/181]'),
    ('5.3.2025000000.6', [1916, 210, -70, -35, 0, 1], '[1, a, a^2, a^3, 1/446*a^4 + 55/223*a^3 + 23/446*a^2 - 108/223*a + 44/223]'),
    ('5.1.2025000000.5', [-232, -15, -40, 10, 0, 1], '[1, a, a^2, 1/4*a^3 - 1/2*a^2 - 1/4*a, 1/4*a^4 - 1/4*a^2 - 1/2*a]'),
    ('5.1.2025000000.8', [612, 210, -10, -15, 0, 1], '[1, a, a^2, a^3, 1/282*a^4 + 9/47*a^3 + 27/94*a^2 + 67/141*a + 19/47]'),
    ('5.1.2025000000.9', [868, 435, -40, -40, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/12*a^4 + 1/12*a^3 - 1/4*a^2 + 5/12*a - 1/3]'),
    ('5.3.3037500000.1', [-666, -765, -330, -60, 0, 1], '[1, a, a^2, 1/6*a^3 - 1/2*a, 1/12*a^4 - 1/12*a^3 + 1/4*a^2 + 1/4*a - 1/2]'),
    ('5.1.3037500000.1', [-2088, -390, -10, -15, 0, 1], '[1, a, a^2, 1/3*a^3 + 1/3*a^2 + 1/3*a, 1/1182*a^4 - 91/591*a^3 + 13/1182*a^2 - 2/197*a - 95/197]'),
    ('5.1.3037500000.3', [-288, 360, -60, -15, 0, 1], '[1, a, a^2, 1/6*a^3 - 1/2*a, 1/24*a^4 + 3/8*a^2 - 1/2*a]'),
    ('5.1.3037500000.7', [2200, 750, -100, -25, 0, 1], '[1, a, a^2, 1/5*a^3, 1/1110*a^4 - 34/555*a^3 - 19/74*a^2 + 41/111*a - 49/111]'),
    ('5.1.3645000000.4', [-888, 915, -220, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/344*a^4 + 57/344*a^3 + 153/344*a^2 - 99/344*a + 11/43]'),
    ('5.3.5695312500.2', [-60, 150, -200, -75, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/166*a^4 + 27/166*a^3 - 5/83*a^2 + 14/83*a + 38/83]'),
    ('5.1.5695312500.1', [-390, 1275, -350, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/1068*a^4 - 43/1068*a^3 - 287/1068*a^2 + 81/356*a + 73/178]'),
    ('5.1.5695312500.2', [-120, -75, -50, 0, 0, 1], '[1, a, a^2, a^3, 1/14*a^4 - 3/14*a^3 - 5/14*a^2 - 1/2*a + 1/7]'),
    ('5.3.6075000000.7', [1764, 735, -80, -60, 0, 1], '[1, a, a^2, 1/6*a^3 + 1/3*a^2 + 1/6*a, 1/84*a^4 - 1/12*a^3 - 11/84*a^2 - 1/28*a]'),
    ('5.1.6075000000.1', [144, 360, -30, 15, 0, 1], '[1, a, a^2, 1/6*a^3 - 1/2*a, 1/84*a^4 - 1/14*a^3 - 11/28*a^2 + 2/7]'),
    ('5.1.9112500000.1', [-3600, 0, -150, -75, 0, 1], '[1, a, 1/2*a^2 - 1/2*a, 1/60*a^3 - 1/4*a^2 - 1/2*a, 1/60*a^4 - 1/4*a^2 - 1/2*a]'),
    ('5.1.9112500000.3', [-1800, 1500, -50, 75, 0, 1], '[1, a, a^2, 1/10*a^3 - 1/2*a, 1/120*a^4 - 1/20*a^3 + 1/8*a^2 - 1/6*a - 1/2]'),
    ('5.3.10125000000.1', [-4320, -1725, -100, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/192*a^4 + 11/64*a^3 - 21/64*a^2 - 67/192*a - 1/2]'),
    ('5.3.10125000000.3', [480, 0, -150, -25, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/248*a^4 + 3/62*a^3 + 119/248*a^2 + 19/124*a - 5/31]'),
    ('5.1.10125000000.1', [-4860, 1350, -150, 75, 0, 1], '[1, a, a^2, 1/6*a^3 - 1/2*a^2, 1/432*a^4 + 1/48*a^3 - 5/36*a^2 - 7/72*a + 1/4]'),
    ('5.5.10125000000.1', [480, 0, -250, -75, 0, 1], '[1, a, 1/2*a^2 - 1/2*a, 1/4*a^3 - 1/4*a^2 - 1/2*a, 1/16*a^4 + 1/16*a^2 - 3/8*a - 1/2]'),
    ('5.1.10125000000.12', [-780, 150, -150, 75, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/1904*a^4 - 375/1904*a^3 - 7/68*a^2 - 453/952*a - 229/476]'),
    ('5.1.10125000000.17', [-60, 75, 0, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/4*a^4 - 1/4*a^3 + 1/4*a^2 - 1/4*a]'),
    ('5.1.10125000000.20', [5820, 2250, -50, -75, 0, 1], '[1, a, a^2, a^3, 1/1982*a^4 - 157/991*a^3 - 579/1982*a^2 - 294/991*a + 287/991]'),
    ('5.3.12000000000.4', [480, -450, -200, 0, 0, 1], '[1, a, a^2, 1/3*a^3 + 1/3*a^2, 1/702*a^4 + 7/351*a^3 + 98/351*a^2 - 44/117*a + 11/117]'),
    ('5.3.15187500000.3', [-160, -150, -50, -25, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/24*a^4 + 5/24*a^3 - 1/2*a^2 - 1/12*a + 1/3]'),
    ('5.3.15187500000.5', [320, 1200, -350, -25, 0, 1], '[1, a, a^2, 1/26*a^3 - 2/13*a^2 - 1/26*a + 6/13, 1/312*a^4 - 1/78*a^3 - 35/104*a^2 + 71/156*a + 1/3]'),
    ('5.3.15187500000.8', [920, -150, -50, -25, 0, 1], '[1, a, a^2, 1/14*a^3 - 1/14*a^2 - 3/7*a - 3/7, 1/42*a^4 - 1/42*a^3 - 1/7*a^2 - 10/21*a + 1/3]'),
    ('5.1.15187500000.9', [-360, 300, -100, 0, 0, 1], '[1, a, 1/2*a^2, 1/4*a^3 - 1/2*a, 1/12*a^4 - 1/3*a]'),
    ('5.1.15187500000.10', [-320, 0, -50, 25, 0, 1], '[1, a, 1/2*a^2 - 1/2*a, 1/2*a^3 - 1/2*a, 1/24*a^4 - 1/6*a^3 + 5/24*a^2 - 5/12*a - 1/3]'),
    ('5.1.15187500000.11', [-240, 450, -150, 25, 0, 1], '[1, a, a^2, a^3, 1/334*a^4 + 45/167*a^3 + 109/334*a^2 - 13/167*a + 57/167]'),
    ('5.1.15187500000.13', [910, 1125, -50, -50, 0, 1], '[1, a, a^2, 1/6*a^3 - 1/3*a^2 + 1/6*a - 1/3, 1/396*a^4 + 23/396*a^3 + 83/396*a^2 - 11/36*a - 37/198]'),
    ('5.1.15187500000.14', [3840, 1500, -100, -75, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/12*a^4 - 1/6*a^3 + 1/12*a^2 - 1/2*a]'),
    ('5.3.18225000000.2', [10368, 2160, -240, -90, 0, 1], '[1, a, 1/2*a^2, 1/12*a^3 - 1/2*a, 1/144*a^4 - 1/8*a^2 + 1/3*a]'),
    ('5.1.18225000000.1', [-5184, 2160, -120, 90, 0, 1], '[1, a, 1/2*a^2, 1/12*a^3 - 1/2*a, 1/144*a^4 + 1/8*a^2 + 1/6*a]'),
    ('5.1.91125000000.1', [-15720, -525, -100, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/22728*a^4 + 1519/22728*a^3 - 10895/22728*a^2 - 1207/7576*a - 27/947]'),
    ('5.1.91125000000.6', [-1740, 1275, -200, 0, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a, 1/452*a^4 + 53/452*a^3 + 97/452*a^2 - 31/452*a + 21/113]'),
    ('5.1.91125000000.16', [28260, 8025, -100, -150, 0, 1], '[1, a, a^2, 1/24*a^3 - 1/12*a^2 - 5/24*a - 1/2, 1/504*a^4 + 1/168*a^3 - 5/168*a^2 + 107/504*a + 13/42]'),
]

DEGREE6_EXAMPLES = [
    ('6.2.7381125000000.77', [3220, 96, -270, -140, -15, 0, 1], '[1, a, a^2, 1/2*a^3 - 1/2*a^2, 1/2*a^4 - 1/2*a^2, 1/15266*a^5 + 1265/15266*a^4 - 80/449*a^3 - 3045/7633*a^2 + 2605/7633*a - 2083/7633]'),
]

DEGREE8_EXAMPLES = [
    (None, [1, 0, 1, 0, 2, 0, -1, 0, 1], '[1, a, a^2, a^3, a^4, a^5, 1/2*a^6 - 1/2, 1/2*a^7 - 1/2*a]'),
]


def generate_examples(table, out_dir, lean_root, native=False, only=None,
                      with_discr=False):
    """Regenerate one batch of the predecessor project from a table of rows."""
    Rx = PolynomialRing(ZZ, 'x')
    Qa = PolynomialRing(QQ, 'a')
    a = Qa.gen()
    for i, (label, coeffs, basis) in enumerate(table):
        if only is not None and i not in only:
            continue
        B = basis(a) if callable(basis) else sage_eval(basis, locals={'a': a})
        generate_ring_of_integers_lean(Rx(coeffs), B, i, label=label,
                                       out_dir=out_dir, lean_root=lean_root,
                                       native=native, with_discr=with_discr)


def generate_degree3_examples(out_dir='IdealArithmetic/DedekindProject/Degree3Examples',
                              lean_root='IdealArithmetic.DedekindProject.Degree3Examples',
                              native=False, only=None, with_discr=True):
    generate_examples(DEGREE3_EXAMPLES, out_dir, lean_root, native, only, with_discr)


def generate_degree5_examples(out_dir='IdealArithmetic/DedekindProject/Degree5Examples',
                              lean_root='IdealArithmetic.DedekindProject.Degree5Examples',
                              native=False, only=None, with_discr=False):
    generate_examples(DEGREE5_EXAMPLES, out_dir, lean_root, native, only, with_discr)


def generate_degree6_examples(out_dir='IdealArithmetic/DedekindProject/Degree6Examples',
                              lean_root='IdealArithmetic.DedekindProject.Degree6Examples',
                              native=False, only=None, with_discr=False):
    generate_examples(DEGREE6_EXAMPLES, out_dir, lean_root, native, only, with_discr)


def generate_degree8_examples(out_dir='IdealArithmetic/DedekindProject/Degree8Example',
                              lean_root='IdealArithmetic.DedekindProject.Degree8Example',
                              native=False, only=None, with_discr=False):
    generate_examples(DEGREE8_EXAMPLES, out_dir, lean_root, native, only, with_discr)
