import IdealArithmetic.MordellExamples.MordellExample17.NF3_1_1836_2.EmbeddingApprox3_1_1836_2
import IdealArithmetic.MordellThueProject.ArtinInequality

/-!
# `zeta1` is a fundamental unit of `O`

Every unit of `O` is `± zeta1 ^ n`.  `artin_inequality_bound_index'` is fed with
`a/b = 5/2` and `c/d = 4/1`, giving the index bound `(c*b)/(a*d) = 8/5 = 1`.
There is no prime `≤ 1`, so the saturation hypothesis `hp` is vacuous and this field needs no
`UnitsSaturated` certificate at all.

Opus 5
-/

set_option linter.all false

open NumberField NumberField.ComplexEmbedding
open scoped Classical

namespace NF3_1_1836_2

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

/-- **Every unit of `O` is `± zeta1 ^ n`.** -/
theorem units_eq_zpow_Z1 : ∀ u : Oˣ, ∃ n : ℤ, u = Z1 ^ n ∨ u = -Z1 ^ n := by
  obtain ⟨σ, hσ⟩ := exists_not_isReal_K
  refine artin_inequality_bound_index' K_finrank σ _
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign) hσ
    O_integral_closure Z1 5 2 4 1 (by norm_num) (by norm_num) ?_ disc_pow_bound ?_ ?_ ?_
  · rw [K_discr]; norm_num
  · rw [Z1_coe]; exact zeta1_embedding_one_lt
  · rw [Z1_coe]; exact zeta1_pow_le_two_pow
  · exact fun p hp hple => absurd (hp.two_le.trans hple) (by norm_num)

end

end NF3_1_1836_2
