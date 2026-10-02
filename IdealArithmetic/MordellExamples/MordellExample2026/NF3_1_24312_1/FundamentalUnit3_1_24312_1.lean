import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.EmbeddingApprox3_1_24312_1
import IdealArithmetic.MordellThueProject.ArtinInequality
import IdealArithmetic.Computation.PrimeSieve

/-!
# `zeta1` is a fundamental unit of `O`

Every unit of `O` is `± zeta1 ^ n`.  The proof feeds `artin_inequality_bound_index'` with
`a/b = 4/1` and `c/d = 99/1`, so the index bound is `(c*b)/(a*d) = 99/4 = 24`, and the
hypothesis `hp` is discharged for the nine primes `p ≤ 24` by the certificates `NPCU p`.

Opus 5
-/

set_option linter.all false

open NumberField NumberField.ComplexEmbedding
open scoped Classical

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

/-- Reduce a statement about all primes `p ≤ B` to the explicit list `primesBetween 1 B L`. -/
lemma forall_prime_le_of_forall_mem_primesBetween {B : ℕ} {L : List ℕ}
    (hL : ∀ q, Nat.Prime q → q < Nat.sqrt B + 1 → q ∈ L) (hpL : ¬ 1 ∈ L)
    {P : ℕ → Prop} (H : ∀ p ∈ primesBetween 1 B L, P p) :
    ∀ p, Nat.Prime p → p ≤ B → P p := fun p hp hpB =>
  H p ((primesBetween_mem 1 B le_rfl L hL hpL p).mpr ⟨hp, hp.one_lt, hpB⟩)

/-- The `hp` hypothesis of `artin_inequality_bound_index'`, for every prime `p ≤ 24`. -/
lemma hp_Z1 : ∀ p, Nat.Prime p → p ≤ 24 →
    ∀ u : Oˣ, ∃ (e : ℤ) (t : Oˣ), u = Z1 ^ e * t ^ p ∨ u = -Z1 ^ e * t ^ p := by
  refine forall_prime_le_of_forall_mem_primesBetween (L := [2, 3, 5]) ?_ (by decide) ?_
  · intro q hq hq5
    rw [show Nat.sqrt 24 = 4 from by symm; rw [Nat.eq_sqrt']; decide] at hq5
    have := hq.two_le
    interval_cases q
    · decide
    · decide
    · exact absurd hq (by decide)
  · rw [show primesBetween 1 24 [2, 3, 5] = [2, 3, 5, 7, 11, 13, 17, 19, 23] from by decide]
    have hAu : ∀ i, (![zeta1] : Fin 1 → O) i = (Z1 : O) := fun i => by
      fin_cases i; exact (IsUnit.unit_spec isUnit_zeta1).symm
    -- `p = 2` divides the torsion order, so it uses the `DvdT` certificate
    have h2 := units_pow_of_pMaximalUnitsCertificateDvdT K_finrank O_integral_closure Z1
      NPCU2 rfl hAu
    -- the odd primes use the `NDvdT` certificates, whose conclusion has no sign
    have hodd : ∀ (p : ℕ) (A : pMaximalUnitsCertificateNDvdT O p), A.r = 1 →
        (∀ i, A.u i = (Z1 : O)) →
        ∀ u : Oˣ, ∃ (e : ℤ) (t : Oˣ), u = Z1 ^ e * t ^ p ∨ u = -Z1 ^ e * t ^ p := by
      intro p A hAr hA u
      obtain ⟨e, t, h⟩ := units_pow_of_pMaximalUnitsCertificateNDvdT O_integral_closure Z1 A hAr hA u
      exact ⟨e, t, Or.inl h⟩
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h2
    · exact hodd 3 NPCU3 rfl hAu
    · exact hodd 5 NPCU5 rfl hAu
    · exact hodd 7 NPCU7 rfl hAu
    · exact hodd 11 NPCU11 rfl hAu
    · exact hodd 13 NPCU13 rfl hAu
    · exact hodd 17 NPCU17 rfl hAu
    · exact hodd 19 NPCU19 rfl hAu
    · exact hodd 23 NPCU23 rfl hAu

/-- **Every unit of `O` is `± zeta1 ^ n`.** -/
theorem units_eq_zpow_Z1 : ∀ u : Oˣ, ∃ n : ℤ, u = Z1 ^ n ∨ u = -Z1 ^ n := by
  obtain ⟨σ, hσ⟩ := exists_not_isReal_K
  refine artin_inequality_bound_index' K_finrank σ _
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign) hσ
    O_integral_closure Z1 4 1 99 1 (by norm_num) (by norm_num) ?_ disc_pow_bound ?_ ?_ ?_
  · rw [K_discr]; norm_num
  · rw [Z1_coe]; exact zeta1_embedding_one_lt
  · rw [Z1_coe]; exact zeta1_pow_le_two_pow
  · simpa using hp_Z1

end

/-! ### The same, packaged as a fundamental system of `𝓞 K` -/

noncomputable section

/-- `zeta1` as a unit of the ring of integers. -/
def W1 : (RingOfIntegers K)ˣ :=
  Units.map (Subalgebra.equivOfEq O _ O_integral_closure).toRingHom.toMonoidHom Z1

lemma W1_coe : (algebraMap (RingOfIntegers K) K) (W1 : RingOfIntegers K) = (zeta1 : K) := by
  rw [W1]
  simp only [Units.coe_map, RingEquiv.toRingHom_eq_coe, MonoidHom.coe_coe, RingHom.coe_coe]
  exact Z1_coe

/-- Every unit of `𝓞 K` is `± W1 ^ n`. -/
theorem units_eq_zpow_W1 : ∀ u : (RingOfIntegers K)ˣ, ∃ n : ℤ, u = W1 ^ n ∨ u = -W1 ^ n := by
  obtain ⟨σ, hσ⟩ := exists_not_isReal_K
  refine artin_inequality_bound_index'' K_finrank σ _
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign) hσ
    O_integral_closure Z1 W1 ?_ 4 1 99 1 (by norm_num) (by norm_num) ?_ disc_pow_bound ?_ ?_ ?_
  · rw [W1_coe, Z1_coe]
  · rw [K_discr]; norm_num
  · rw [Z1_coe]; exact zeta1_embedding_one_lt
  · rw [Z1_coe]; exact zeta1_pow_le_two_pow
  · simpa using hp_Z1

/-- `K` has unit rank `1`: one real place and one complex place. -/
lemma K_unitRank : NumberField.Units.rank K = 1 := by
  rw [NumberField.Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    K_nrRealPlaces, K_nrComplexPlaces]

/-- A fundamental system of units of `K`, in the shape of `NumberField.Units.fundSystem`:
the single unit `zeta1`. -/
def fundSystemZeta1 : Fin (NumberField.Units.rank K) → (RingOfIntegers K)ˣ := fun _ => W1

/-- Together with the torsion, `fundSystemZeta1` generates all of `(𝓞 K)ˣ` -- the defining
property of a fundamental system, cf. `NumberField.Units.closure_fundSystem_sup_torsion_eq_top`. -/
theorem closure_fundSystemZeta1_sup_torsion_eq_top :
    Subgroup.closure (Set.range fundSystemZeta1) ⊔ NumberField.Units.torsion K = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro x
  have hW1mem : W1 ∈ Subgroup.closure (Set.range fundSystemZeta1) :=
    Subgroup.subset_closure ⟨⟨0, by rw [K_unitRank]; norm_num⟩, rfl⟩
  obtain ⟨n, hn | hn⟩ := units_eq_zpow_W1 x
  · exact hn ▸ Subgroup.mem_sup_left (Subgroup.zpow_mem _ hW1mem n)
  · refine hn ▸ ?_
    rw [show (-W1 ^ n : (RingOfIntegers K)ˣ) = (-1) * W1 ^ n from (neg_one_mul _).symm]
    exact mul_mem (Subgroup.mem_sup_right neg_one_mem_torsion)
      (Subgroup.mem_sup_left (Subgroup.zpow_mem _ hW1mem n))

end
