###############################################################################
#  UnitsSaturationNFLean.sage
#
#  `InvariantsNFLean.sage` without the class group: for a cubic number field it
#  certifies that `O` is the ring of integers, computes `disc K` and the
#  signature, and builds
#
#      pMaximalUnitsCertificateDvdT   for p = 2,
#      pMaximalUnitsCertificateNDvdT  for odd primes p <= B,
#
#  For a cubic field the torsion is {+-1}, of order 2, so p divides the torsion
#  order exactly when p = 2; that is the only place the two cases differ.
#
#  No class group, class number, Minkowski bound or ideal-saturation data.
#
#  Files written to {lean_root}/NF{num}/ :
#      Irreducible{num}.lean
#      RI{num}.lean
#      UnitsData{num}.lean
#      UnitsSaturated{num}_{p}.lean       (one per prime p <= B)
#      Invariants{num}.lean
#
#  Entry point: generate_units_proof_lean(T, B_polys, num, B, lean_root=...)
###############################################################################

load('InvariantsNFLean.sage')



def _wrap_ns(body, num):
    """Wrap a generated Lean file in `namespace NF{num} ... end NF{num}` (see
    InvariantsNFLean.sage for why: two examples otherwise collide on `T`, `K`, `O`, ...)."""
    lines = body.split("\n")
    idx = [i for i, l in enumerate(lines) if l.startswith("import")]
    if not idx:
        return body
    openers = sum(1 for l in lines
                  if re.match(r'^\s*(noncomputable\s+)?section\b', l) or re.match(r'^\s*namespace\b', l))
    closers = sum(1 for l in lines if re.match(r'^\s*end\b', l))
    lines.insert(idx[-1] + 1, "\nnamespace NF" + str(num))
    out = "\n".join(lines).rstrip()
    out += "\n" + "\nend\n" * max(0, openers - closers) + "\nend NF" + str(num) + "\n"
    return out

def MatrixPrimesUnits(K, O, p, u, search_bound=400, max_bound=50000):
    """Units-only analogue of `MatrixPrimesG`.

    `u` is the unit system `[torsion generator] + [fundamental units]`, passed in
    rather than recomputed so that it is exactly the one `UnitsDataLean` writes
    out: the discrete logs below must be those of the *same* elements, or
    `hxeq := rfl` in the generated `DiscreteLogCertificate` is false.

    Returns `(A, Ql, L, flag)`: `L` lists the fundamental units, followed by the
    torsion generator when `p` divides its order (then `flag = 1`); `Ql` are
    degree-one primes over rational primes `q = 1 mod p` chosen so that the
    matrix `A` of discrete logarithms of `L` modulo `Ql` is invertible over
    `GF(p)`.  Unlike `MatrixPrimesG` there is nothing to reorder, since there are
    no class group elements to place last.

    Usable `q` must both be `1 mod p` and admit a degree-one prime of `K`, which
    gets sparse for larger `p`, so the search window grows until it succeeds.
    """
    flag = 1 if K(u[0]).multiplicative_order() % p == 0 else 0
    L = [K(w) for w in u[1:]] + ([K(u[0])] if flag else [])
    A, Ql = [], []
    lo, hi = 2, search_bound + 1
    while len(Ql) < len(L) and lo <= max_bound:
        for q in primes(lo, hi):
            if q == p or (q - 1) % p != 0:
                continue
            z = primitive_root(q)
            for Q, _ in factor(K.ideal(q)):
                if Q.norm() != q or any(K(x) in Q for x in L):
                    continue
                row = [DiscreteLog(O, Q, L[j], z)[0] % p for j in range(len(L))]
                if Matrix(GF(p), A + [row]).rank() > len(Ql):
                    A, Ql = A + [row], Ql + [Q]
                if len(Ql) == len(L):
                    break
            if len(Ql) == len(L):
                break
        lo, hi = hi, min(4 * hi, max_bound + 1)
    if len(Ql) < len(L):
        raise ValueError(
            f"MatrixPrimesUnits: no full-rank system for p={p} below {max_bound}")
    return Matrix(A), Ql, [K(x) for x in L], flag


def NormalizeUnitRealGt1(K, w, extra=512):
    """Replace `w` by whichever of `+-w^{+-1}` has value `> 1` under the first real
    embedding of `K`.

    `unit_group().gens()` gives no sign or direction guarantee -- for
    `x^3+3x-90` Sage's generator has real value `-2.06e-30` -- whereas the
    Artin inequality is stated for a unit that is genuinely `> 1` there.
    The embedding is evaluated at a precision scaled to the coordinates of `w`,
    since the value can be many orders of magnitude smaller than they are.
    """
    embs_count = K.signature()[0]
    if embs_count == 0:
        return w
    co = [QQ(c) for c in K(w).list()]
    prec = 4 * max(ZZ(c.numerator()).nbits() + ZZ(c.denominator()).nbits()
                   for c in co) + extra
    RF = RealField(prec)
    phi = K.real_embeddings(prec)[0]
    val = RF(phi(w))
    if val.is_zero():
        raise ValueError("NormalizeUnitRealGt1: embedding underflowed; raise `extra`")
    if abs(val) < 1:
        w = w ** (-1)
        val = RF(phi(w))
    if val < 0:
        w, val = -w, -val
    if not val > 1:
        raise ValueError(f"NormalizeUnitRealGt1: could not normalise, value {val}")
    return w


def UnitsDataLean(K, B, num, u, lean_root='IdealArithmetic.Examples'):
    """`UnitsData{num}.lean`: the torsion generator `v`, the fundamental units
    `zeta{i}`, their `IsUnit` proofs and `v_pow_one`.  Returns `(str, order(v))`."""
    out = f"""import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import {lean_root}.NF{num}.RI{num}

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

"""
    names = ['v'] + [f'zeta{i + 1}' for i in range(len(u) - 1)]
    for i in range(len(names)):
        out += (f'def {names[i]} := B.equivFun.symm '
                + ExList(str(elems_to_basis([u[i]], B).list())) + '\n\n')
    out += IsUnitInvLean(B, u[1:], names[1:])
    torsion_out, order_v = TorsionUnitProof(K, B, u[0], 'v')
    return out + torsion_out, order_v


def UnitsSaturatedLean(K, B, num, Ql_gens, p, elems, names, prefix,
                       lean_root='IdealArithmetic.Examples'):
    """`UnitsSaturated{num}_{p}.lean`: the prime ideals `I{i}`, their norms `N{i}`,
    the primitive-root certificates `R{q}` and the discrete logs `Log{i}{j}`,
    all inside `namespace {prefix}`."""
    out = f"""import {lean_root}.NF{num}.UnitsData{num}
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import {lean_root}.NF{num}.RI{num}

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace {prefix} \n"""
    sub_out, _, _ = DiscreteLogListLean(K, B, Ql_gens, 'I', p, elems, names)
    return out + sub_out + f"end {prefix}\n"


def build_units_invariants_content(T, K, B, num, bad, flagl, flaglW, flagD,
                                   u, order_v, primes_B, local_data, D,
                                   lean_root='IdealArithmetic.Examples'):
    """`Invariants{num}.lean`: ring of integers, discriminant, signature, the rank
    certificate `RC`, and `NPCU{p}` for every `p` in `primes_B`."""
    out = ""
    T_lean = str(T).replace('x', 'X')
    d = K.degree()

    for p in primes_B:
        out += f'import {lean_root}.NF{num}.UnitsSaturated{num}_{p}\n'
    out += f"""import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Signature.ResultantRecursive
import IdealArithmetic.DedekindProject.Discriminant

set_option linter.all false

/- Number field `K(α)` with α root of polynomial `{T_lean}`. -/

/- Ring of integers with basis `{B}` -/

open BigOperators Classical Matrix Polynomial Module

noncomputable section

instance hirr : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

instance K_field : Field K := by
  unfold K
  exact AdjoinRoot.instField

instance K_numberField : NumberField K := by
  unfold K
  exact AdjoinRoot.instNumberFieldRat

instance : Module ℚ K := Algebra.toModule
instance : @Algebra ℤ K CommRing.toCommSemiring CommRing.toCommSemiring.toSemiring := Ring.toIntAlgebra K
instance : @CharZero K CommRing.toCommSemiring.toNonAssocSemiring.toAddCommMonoidWithOne.toAddMonoidWithOne := charZero_of_expChar_one' K

lemma K_finrank : Module.finrank ℚ K = {d} := by
  unfold K
  erw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux _), Polynomial.natDegree_map_eq_of_injective, T_degree]
  · simp
  · exact RingHom.injective_int (algebraMap ℤ ℚ)
  · exact Irreducible.ne_zero hirr.out

theorem O_integral_closure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ {bad}
  · fin_cases hc
"""
    for p in bad:
        if flagl[p] == 0:
            if flaglW[p] == 1:
                out += f'    exact @pMaximal_of_MaximalOrderCertificateWLists K {p} _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M{p}\n'
            else:
                out += f'    exact @pMaximal_of_MaximalOrderCertificateLists K {p} _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M{p}\n'
        else:
            out += f'    exact @pMaximal_of_MaximalOrderCertificateOfUnramifiedLists K {p} _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M{p}\n'

    out += f"""  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T _ T_ofList {bad} D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_integral_closure] ; rfl

instance : Module.Finite ℤ (Additive ((↥O)ˣ ⧸ CommGroup.torsion (↥O)ˣ)) := by
  rw [O_integral_closure]
  exact NumberField.Units.instFiniteIntAdditiveQuotientUnitsRingOfIntegersSubgroupTorsion K

instance : Module.Free ℤ (Additive ((↥O)ˣ ⧸ CommGroup.torsion (↥O)ˣ)) := by
  rw [O_integral_closure]
  exact NumberField.Units.instFreeIntAdditiveQuotientUnitsRingOfIntegersSubgroupTorsion K

instance :  Fintype ↥(CommGroup.torsion (↥O)ˣ) := by
  rw [O_integral_closure]
  exact NumberField.Units.instFintypeSubtypeUnitsRingOfIntegersMemSubgroupTorsion K

instance : IsCyclic ↥(CommGroup.torsion (↥O)ˣ) := by
  rw [O_integral_closure]
  exact NumberField.Units.instIsCyclicSubtypeUnitsRingOfIntegersMemSubgroupTorsion K

instance DD' : IsDedekindDomain O  := by
  rw [O_integral_closure]
  exact integralClosure.isDedekindDomain ℤ ℚ K

instance : Module.Free ℤ ↥O := Module.Free.of_basis B

instance  : IdemCommSemiring (Ideal O) := Ideal.instIdemCommSemiring
instance : CharZero O := SubsemiringClass.instCharZero O

"""

    out += RankUnitCertificateLean(T.change_ring(QQ), 'T_ofList', 'Adj',
                                   'O_integral_closure', 'RC')
    out += '\n'

    # One pMaximalUnitsCertificate per prime.  `names` is passed whole: the
    # slice `names[:-len(phi)]` used by `build_invariants_content` would be
    # `names[:0] = []` here, since there are no class group elements.
    for p in primes_B:
        A, names, flag, Ql = local_data[p]
        Qlq = [ZZ(Q.norm()) for Q in Ql]
        if flag == 1:
            out += CertificateMaximalUnitsDvdT(A, p, names[:-1], 'v', order_v,
                                               f'Sat{p}', 'I', Qlq, 'RC')
        else:
            out += pNeDvdTorsionLean(K, B, 'K_finrank', 'O_integral_closure', 'IC', p)
            out += '\n'
            out += CertificateMaximalUnitsNDvdT(A, p, names, f'Sat{p}', 'I', Qlq, 'RC')
        out += '\n'

    if flagD == 1:
        out += f"""
lemma T_discr : T.discr = {T.discriminant()} :=  by
  convert discriminant_eq_DiscriminantOfPRemainder_of_SturmBuilderOfList SturmRC
  rw [T_ofList]

theorem K_discr : NumberField.discr K = {D} := by
  rw [discr_numberField_eq_discrSubalgebraBuilder T_irreducible BQ O_integral_closure]
  rw [T_discr]
  rfl

lemma K_nrComplexPlaces : NumberField.InfinitePlace.nrComplexPlaces K = {K.signature()[1]} := by
  rw [nrComplexPlaces_of_RankUnitsCertificate RC]
  rfl

lemma K_nrRealPlaces : NumberField.InfinitePlace.nrRealPlaces K = {K.signature()[0]} := by
  rw [nrRealPlaces_of_RankUnitsCertificate RC]
  rfl
"""
    return out


def generate_units_proof_lean(T, B_polys, num, B_bound, search_bound=400,
                              lean_root='IdealArithmetic.Examples'):
    """Generate the Lean files certifying unit saturation for all primes p <= B_bound.

    T         : irreducible polynomial in ZZ['x'] (cubic)
    B_polys   : integral basis of the number field
    num       : label for the output directory and file names; '.' is replaced by
                '_' so that LMFDB labels such as '3.1.24312.1' may be passed
                directly (Lean module components cannot contain '.')
    B_bound   : certificates are produced for every prime p <= B_bound
    lean_root : Lean module prefix under which the files are placed.  The output
                directory is this path with '.' replaced by the path separator, so
                imports and on-disk location always agree; it must lie under the
                `IdealArithmetic` lean_lib root, e.g. 'IdealArithmetic.MordellExamples.MordellExample2026'
                writes to IdealArithmetic/MordellExamples/MordellExample2026/NF{num}/.
    """
    num = str(num).replace('.', '_')
    # The Dedekind certificate needs an *integer* Bezout pair; over QQ[x] the gcd is 1 and the
    # cofactors come out rational, which silently produces an invalid certificate.
    T = ZZ['x'](T)
    K = None
    if len(B_polys) > 1 and hasattr(B_polys[1], 'parent'):
        parent0 = B_polys[1].parent()
        if hasattr(parent0, 'number_field'):
            K = parent0.number_field()
        elif isinstance(parent0, NumberField_base):
            K = parent0
    if K is None:
        K = NumberField(T, 'a')
    B = B_polys
    T_lean = str(T).replace('x', 'X')

    folder = os.path.join(lean_root.replace('.', os.sep), f"NF{num}")
    os.makedirs(folder, exist_ok=True)

    # 1. Irreducible{num}.lean
    with open(f"{folder}/Irreducible{num}.lean", "w") as f:
        f.write(_wrap_ns(LeanProofIrreducible(T), num))

    # 2. RI{num}.lean
    ri_str, bad, flagl, flaglW, flagD = LeanProof(T, B, f'Irreducible{num}', num, '', 1)
    ri_str = ri_str.replace(f'IdealArithmetic.Examples.NF{num}', f'{lean_root}.NF{num}')
    with open(f"{folder}/RI{num}.lean", "w") as f:
        f.write(_wrap_ns(ri_str, num))

    # 3. UnitsData{num}.lean
    O = K.ring_of_integers()
    # Fundamental units are normalised to be > 1 under the real embedding; the
    # torsion generator u[0] is left alone (it has absolute value 1).
    u = [K(g) for g in K.unit_group(proof=False).gens()]
    u = [u[0]] + [NormalizeUnitRealGt1(K, w) for w in u[1:]]
    set_random_seed(10)
    units_str, order_v = UnitsDataLean(K, B, num, u, lean_root)
    with open(f"{folder}/UnitsData{num}.lean", "w") as f:
        f.write(_wrap_ns(units_str, num))

    # 4. UnitsSaturated{num}_{p}.lean, one per prime p <= B_bound
    primes_B = list(primes(B_bound + 1))
    local_data = {}
    for p in primes_B:
        A, Ql, elems, flag = MatrixPrimesUnits(K, O, p, u, search_bound)
        r = len(elems) - flag
        names = [f'zeta{j + 1}' for j in range(r)] + (['v'] if flag else [])
        local_data[p] = [A, names, flag, Ql]
        Ql_gens = [list(Q.gens()) for Q in Ql]
        set_random_seed(10)
        with open(f"{folder}/UnitsSaturated{num}_{p}.lean", "w") as f:
            f.write(_wrap_ns(UnitsSaturatedLean(K, B, num, Ql_gens, p, elems, names,
                                               f'Sat{p}', lean_root), num))

    # 5. Invariants{num}.lean
    inv_str = build_units_invariants_content(
        T, K, B, num, bad, flagl, flaglW, flagD,
        u, order_v, primes_B, local_data, K.discriminant(), lean_root
    )
    with open(f"{folder}/Invariants{num}.lean", "w") as f:
        f.write(_wrap_ns(inv_str, num))

    print(f"Generated Lean files in {folder}/ "
          f"(unit saturation certificates for p <= {B_bound})")
