import IdealArithmetic.DedekindProject.Discriminant.Discriminant
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.CertifyAdjoinRoot
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers.DedekindCriteria
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.Conductor
import Mathlib.RingTheory.Ideal.Maps

open Polynomial

-- Specifications are human written.
-- Proofs are written with the help of Claude Code Opus 5.

section General
variable {n : ℕ} [NeZero n] {R Q K : Type*} [CommRing R] [IsDomain R] [DecidableEq R]
  [Field Q] [CommRing K] [Algebra Q K] [Algebra R Q] [Algebra R K] [IsScalarTower R Q K]
  [IsFractionRing R Q] {T : R[X]} {l : List R}

/-- The common denominator `d` lies in the conductor of `R[θ]` inside the subalgebra. -/
lemma prod_mem_conductor (A : SubalgebraBuilderLists n R Q K T l)
    (h : (A.h).root ∈ subalgebraOfBuilderLists T l A) :
    algebraMap R (subalgebraOfBuilderLists T l A) A.d ∈
      conductor R (⟨A.h.root, h⟩ : subalgebraOfBuilderLists T l A) := by
  have hq : (algebraMap R Q) A.d ≠ 0 := fun hc =>
    A.hd (IsFractionRing.injective R Q (by rw [hc, map_zero]))
  have hcast : algebraMap R K A.d = A.h.map (C ((algebraMap R Q) A.d)) := by
    rw [← IsAdjoinRoot.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have key : ∀ i, (algebraMap R K A.d) *
      (((basisOfBuilderLists T l A) i : ↥(subalgebraOfBuilderLists T l A)) : K)
      = aeval A.h.root (ofList (List.ofFn (A.B i))) := by
    intro i
    rw [basisOfBuilderLists_apply, hcast, ← map_mul, ← mul_assoc, ← C_mul,
      mul_inv_cancel₀ hq, C_1, one_mul, ← IsAdjoinRoot.aeval_root_eq_map, aeval_map_algebraMap]
  have key' : ∀ i, (algebraMap R (subalgebraOfBuilderLists T l A) A.d) *
      (basisOfBuilderLists T l A) i
      = aeval (⟨A.h.root, h⟩ : ↥(subalgebraOfBuilderLists T l A))
          (ofList (List.ofFn (A.B i))) := by
    intro i
    apply Subtype.ext
    push_cast
    rw [key i]
  intro b
  obtain ⟨c, rfl⟩ : ∃ c : Fin n → R, b = ∑ i, c i • (basisOfBuilderLists T l A) i :=
    ⟨fun i => (basisOfBuilderLists T l A).repr b i, (Module.Basis.sum_repr _ b).symm⟩
  rw [Finset.mul_sum]
  refine Subalgebra.sum_mem _ (fun i _ => ?_)
  rw [mul_smul_comm, key' i]
  exact Subalgebra.smul_mem _ (Polynomial.aeval_mem_adjoin_singleton R _) _

lemma conductor_coprime_of_isCoprime (A : SubalgebraBuilderLists n R Q K T l)
    (h : (A.h).root ∈ subalgebraOfBuilderLists T l A) (c : R) (hc : IsCoprime A.d c) :
    Ideal.comap (algebraMap R (subalgebraOfBuilderLists T l A)) (conductor R ⟨A.h.root, h⟩)
      ⊔ Ideal.span {c} = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hd : A.d ∈ Ideal.comap (algebraMap R (subalgebraOfBuilderLists T l A))
      (conductor R (⟨A.h.root, h⟩ : subalgebraOfBuilderLists T l A)) :=
    Ideal.mem_comap.mpr (prod_mem_conductor A h)
  obtain ⟨u, v, huv⟩ := hc
  rw [← huv]
  exact Ideal.add_mem _
    (Ideal.mul_mem_left _ _ (Ideal.mem_sup_left hd))
    (Ideal.mul_mem_left _ _ (Ideal.mem_sup_right (Ideal.subset_span rfl)))

lemma minpoly_root_subalgebra (A : SubalgebraBuilderLists n R Q K T l)
    (h : (A.h).root ∈ subalgebraOfBuilderLists T l A) :
    minpoly R (⟨A.h.root, h⟩ : subalgebraOfBuilderLists T l A) = ofList l := by
  have hm : Monic T := Polynomial.monic_of_natDegree_le_of_coeff_eq_one n
    (le_of_eq (SubalgebraBuilderOfList _ _ A).hdeg) ((SubalgebraBuilderOfList _ _ A).hm)
  have hminQ : minpoly Q A.h.root = T.map (algebraMap R Q) := by
    rw [IsAdjoinRoot.minpoly_root A.h (Monic.ne_zero (Monic.map (algebraMap R Q) hm)),
      Monic.map _ hm, inv_one, map_one, mul_one]
  have hminR : minpoly R A.h.root = T :=
    Algebra.minpoly_fraction_field T hm A.h.root hminQ
  refine Eq.trans ?_ A.hofL
  refine Eq.trans ?_ hminR
  exact (minpoly.algebraMap_eq Subtype.val_injective _).symm

lemma root_coord_subalgebraBuilder (A : SubalgebraBuilderLists n R Q K T l)(a : Fin n → R) (g : List R)
    (h : (List.sum (List.ofFn (fun i => [a i] * (List.ofFn (A.B i))))).dropTrailingZeros' =
    ([(A.d)] * [0, 1] - l * g).dropTrailingZeros' ) :
    (timesTableOfSubalgebraBuilderLists T l A).basis.equivFun.symm a =
      ⟨A.h.root, root_in_subalgebra_lists T l A a g h⟩ := by
  have hq : (algebraMap R Q) A.d ≠ 0 := fun hc =>
    A.hd (IsFractionRing.injective R Q (by rw [hc, map_zero]))
  have hpoly : ∑ i, C (a i) * (ofList (List.ofFn (A.B i))) = C A.d * X - T * (ofList g) := by
    apply_fun Polynomial.ofList at h
    simp only [← dropTrailingZeros_eq_dropTrailingZeros', ofList_dropTrailingZeros_eq_ofList,
      list_sum_eq_ofList_sum, ofList_convolve_eq_mul, ofList_singleton] at h
    convert h
    erw [ofList_addPointwise_eq_add, List.neg_eq_neg_one_mul, ofList_convolve_eq_mul,
      ofList_convolve_eq_mul, ofList_convolve_eq_mul, ← A.hofL]
    simp only [ofList_cons, ofList_nil, mul_zero, add_zero, map_zero,
      map_one, mul_one, zero_add, map_neg, neg_mul, one_mul]
    rfl
  have hmapped : ∑ i, C ((algebraMap R Q) (a i)) *
      (map (algebraMap R Q) (ofList (List.ofFn (A.B i))))
      = C ((algebraMap R Q) A.d) * X
        - (map (algebraMap R Q) T) * (map (algebraMap R Q) (ofList g)) := by
    apply_fun map (algebraMap R Q) at hpoly
    simpa only [Polynomial.map_sum, Polynomial.map_sub, Polynomial.map_mul, map_C, map_X]
      using hpoly
  apply Subtype.ext
  show ((basisOfBuilderLists T l A).equivFun.symm a : K) = A.h.root
  rw [basisOfBuilderLists_apply_Fn, hmapped, mul_sub, ← mul_assoc, ← C_mul,
    inv_mul_cancel₀ hq, C_1, one_mul, map_sub, IsAdjoinRoot.map_X, ← mul_assoc, map_mul,
    map_mul, IsAdjoinRoot.map_self, mul_zero, zero_mul, sub_zero]

end General

section Int

variable {n : ℕ} [NeZero n] {K : Type*} [CommRing K] [Algebra ℚ K]
  [IsScalarTower ℤ ℚ K] {T : ℤ[X]} {l : List ℤ}

/-- Integer specialisation of `conductor_coprime_of_isCoprime`, with `Int.gcd`. -/
lemma conductor_coprime_of_coprime_int (A : SubalgebraBuilderLists n ℤ ℚ K T l)
    (h : (A.h).root ∈ subalgebraOfBuilderLists T l A) (p : ℕ) (gcd : Int.gcd A.d p = 1) :
    Ideal.comap (algebraMap ℤ (subalgebraOfBuilderLists T l A)) (conductor ℤ ⟨A.h.root, h⟩)
      ⊔ Ideal.span {(p : ℤ)} = ⊤ :=
  conductor_coprime_of_isCoprime A h (p : ℤ) (Int.isCoprime_iff_gcd_eq_one.mpr gcd)

end Int

section BuilderCoords

variable {K : Type*} [Field K] [Algebra ℚ K] {T : ℤ[X]} {l : List ℤ}
  (A : SubalgebraBuilderLists 3 ℤ ℚ K T l)

namespace SubalgebraBuilderLists

/-- The element of `K` with builder coordinates `f`, written as a quadratic in the adjoined
root.  The hypothesis is the identity `∑ f i * B i = d (a₂X² + a₁X + a₀)` in `ℚ[X]`. -/
lemma coe_equivFun_symm_quadratic (f : Fin 3 → ℤ) (a₀ a₁ a₂ : ℚ)
    (h : ∑ i, C ((algebraMap ℤ ℚ) (f i))
          * map (algebraMap ℤ ℚ) (ofList (List.ofFn (A.B i)))
        = C ((algebraMap ℤ ℚ) A.d) * (C a₂ * X ^ 2 + C a₁ * X + C a₀)) :
    (((basisOfBuilderLists T l A).equivFun.symm f : subalgebraOfBuilderLists T l A) : K)
      = (a₂ : K) * A.h.root ^ 2 + (a₁ : K) * A.h.root + (a₀ : K) := by
  have hd0 : (algebraMap ℤ ℚ) A.d ≠ 0 := by simpa using A.hd
  rw [basisOfBuilderLists_apply_Fn, h, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hd0, C_1, one_mul]
  simp only [map_add, map_mul, map_pow, IsAdjoinRoot.map_X, ← IsAdjoinRoot.algebraMap_apply,
    eq_ratCast]

/-- The adjoined root is the second basis vector, `θ = w 1`. -/
lemma root_eq_basis_one (hroot : A.h.root ∈ subalgebraOfBuilderLists T l A)
    (h : map (algebraMap ℤ ℚ) (ofList (List.ofFn (A.B 1))) = C ((algebraMap ℤ ℚ) A.d) * X) :
    (⟨A.h.root, hroot⟩ : subalgebraOfBuilderLists T l A) = basisOfBuilderLists T l A 1 := by
  have hd0 : (algebraMap ℤ ℚ) A.d ≠ 0 := by simpa using A.hd
  refine Subtype.ext ?_
  rw [basisOfBuilderLists_apply, h, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hd0, C_1, one_mul,
    IsAdjoinRoot.map_X]

end SubalgebraBuilderLists

end BuilderCoords
