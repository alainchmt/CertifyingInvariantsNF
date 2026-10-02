import IdealArithmetic.MordellExamples.MordellExample79.NF3_1_948_1.EmbeddingApprox3_1_948_1
import IdealArithmetic.MordellThueProject.ArtinInequality

/-!
# `zeta1` is a fundamental unit of `O`

Every unit of `O` is `± zeta1 ^ n`.  `artin_inequality_bound_index'` is fed with
`a/b = 5/2` and `c/d = 44/3`, giving the index bound `(c*b)/(a*d) = 88/15 = 5`, so
`zeta1` has to be certified non-`p`-th-power for `p = 2, 3, 5`.  `2` divides the torsion
order `2`, hence the `DvdT` certificate `NPCU2`; the odd primes use `NPCU3`, `NPCU5`.

Opus 5
-/

set_option linter.all false

open NumberField NumberField.ComplexEmbedding
open scoped Classical

namespace NF3_1_948_1

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

/-- The `hp` hypothesis of `artin_inequality_bound_index'`, for `p = 2, 3, 5`. -/
lemma hp_Z1 : ∀ p, Nat.Prime p → p ≤ 5 →
    ∀ u : Oˣ, ∃ (e : ℤ) (t : Oˣ), u = Z1 ^ e * t ^ p ∨ u = -Z1 ^ e * t ^ p := by
  have hAu : ∀ i, (![zeta1] : Fin 1 → O) i = (Z1 : O) := fun i => by
    fin_cases i; exact (IsUnit.unit_spec isUnit_zeta1).symm
  -- the odd primes use the `NDvdT` certificates, whose conclusion carries no sign
  have hodd : ∀ (p : ℕ) (A : pMaximalUnitsCertificateNDvdT O p), A.r = 1 →
      (∀ i, A.u i = (Z1 : O)) →
      ∀ u : Oˣ, ∃ (e : ℤ) (t : Oˣ), u = Z1 ^ e * t ^ p ∨ u = -Z1 ^ e * t ^ p := by
    intro p A hAr hA u
    obtain ⟨e, t, h⟩ := units_pow_of_pMaximalUnitsCertificateNDvdT O_integral_closure Z1 A hAr hA u
    exact ⟨e, t, Or.inl h⟩
  intro p hp hple
  have := hp.two_le
  interval_cases p
  · exact units_pow_of_pMaximalUnitsCertificateDvdT K_finrank O_integral_closure Z1 NPCU2 rfl hAu
  · exact hodd 3 NPCU3 rfl hAu
  · exact absurd hp (by decide)
  · exact hodd 5 NPCU5 rfl hAu

/-- **Every unit of `O` is `± zeta1 ^ n`.** -/
theorem units_eq_zpow_Z1 : ∀ u : Oˣ, ∃ n : ℤ, u = Z1 ^ n ∨ u = -Z1 ^ n := by
  obtain ⟨σ, hσ⟩ := exists_not_isReal_K
  refine artin_inequality_bound_index' K_finrank σ _
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign) hσ
    O_integral_closure Z1 5 2 44 3 (by norm_num) (by norm_num) ?_ disc_pow_bound ?_ ?_ ?_
  · rw [K_discr]; norm_num
  · rw [Z1_coe]; exact zeta1_embedding_one_lt
  · rw [Z1_coe]; exact zeta1_pow_le_two_pow
  · simpa using hp_Z1

end

end NF3_1_948_1
