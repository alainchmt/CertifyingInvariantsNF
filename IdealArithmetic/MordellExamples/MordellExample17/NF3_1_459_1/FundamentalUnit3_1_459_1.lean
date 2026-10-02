import IdealArithmetic.MordellExamples.MordellExample17.NF3_1_459_1.EmbeddingApprox3_1_459_1
import IdealArithmetic.MordellThueProject.ArtinInequality

/-!
# `zeta1` is a fundamental unit of `O`

Every unit of `O` is `± zeta1 ^ n`.  `artin_inequality_bound_index'` is fed with `a/b = 9/4`
and `c/d = 11/2`, so the index bound is `(c*b)/(a*d) = 44/18 = 2` and the only prime to
certify is `p = 2`, by the saturation certificate `NPCU2`.

Opus 5
-/

set_option linter.all false

open NumberField NumberField.ComplexEmbedding
open scoped Classical

namespace NF3_1_459_1

noncomputable section

/-- `zeta1` as a unit of `O`. -/
def Z1 : Oˣ := isUnit_zeta1.unit

lemma Z1_coe : ((Z1 : O) : K) = (zeta1 : K) := by rw [Z1, IsUnit.unit_spec]

/-- `K` has a non-real embedding, since it has a complex place. -/
lemma exists_not_isReal_K : ∃ σ : K →+* ℂ, ¬ IsReal σ := by
  have hpos : 0 < Fintype.card { w : InfinitePlace K // w.IsComplex } := by
    rw [show Fintype.card { w : InfinitePlace K // w.IsComplex }
          = InfinitePlace.nrComplexPlaces K from rfl, K_nrComplexPlaces]
    norm_num
  obtain ⟨w, hw⟩ := Fintype.card_pos_iff.mp hpos
  obtain ⟨σ, hσ, -⟩ := hw
  exact ⟨σ, hσ⟩

/-- The `hp` hypothesis of `artin_inequality_bound_index'`: only `p = 2` is in range, and
`2` divides the torsion order, so it is the `DvdT` certificate that applies. -/
lemma hp_Z1 : ∀ p, Nat.Prime p → p ≤ 2 →
    ∀ u : Oˣ, ∃ (e : ℤ) (t : Oˣ), u = Z1 ^ e * t ^ p ∨ u = -Z1 ^ e * t ^ p := by
  intro p hp hple
  obtain rfl : p = 2 := le_antisymm hple hp.two_le
  exact units_pow_of_pMaximalUnitsCertificateDvdT K_finrank O_integral_closure Z1 NPCU2 rfl
    (fun i => by fin_cases i; exact (IsUnit.unit_spec isUnit_zeta1).symm)

/-- **Every unit of `O` is `± zeta1 ^ n`.** -/
theorem units_eq_zpow_Z1 : ∀ u : Oˣ, ∃ n : ℤ, u = Z1 ^ n ∨ u = -Z1 ^ n := by
  obtain ⟨σ, hσ⟩ := exists_not_isReal_K
  refine artin_inequality_bound_index' K_finrank σ _
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign) hσ
    O_integral_closure Z1 9 4 11 2 (by norm_num) (by norm_num) ?_ disc_pow_bound ?_ ?_ ?_
  · rw [K_discr]; norm_num
  · rw [Z1_coe]; exact zeta1_embedding_one_lt
  · rw [Z1_coe]; exact zeta1_pow_le_two_pow
  · simpa using hp_Z1

end

end NF3_1_459_1
