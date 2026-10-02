import IdealArithmetic.MordellExamples.MordellExample142.NF3_1_1704_1.FundamentalUnit3_1_1704_1
import IdealArithmetic.MordellExamples.MordellExample142.NF3_1_1704_1.UnitPowMod3_1_1704_1
import IdealArithmetic.ConductorSubalgebraBuilder
import IdealArithmetic.MordellThueProject.PolyApprox

/-!
# `A ^ 3 + 15 * A ^ 2 * B + 66 * A * B ^ 2 + 106 * B ^ 3 = 1` has exactly 1 solution

The Thue equation produced by the class-group descent for `y² = x³ + 142`.  The Skolem
certificate is at `p = 13`, `f = 12`, and `0` is the only surviving class, so `n = 0` is the
only exponent and `(1, 0)` the only solution.

Opus 5
-/

set_option linter.all false

open Module Polynomial NumberField NumberField.ComplexEmbedding

namespace NF3_1_1704_1

noncomputable section

local notation "θ" => Adj.root

/-- The minimal polynomial of `θ` is the defining cubic. -/
lemma minpoly_root : minpoly ℚ θ = X ^ 3 + Polynomial.C ((15 : ℤ) : ℚ) * X ^ 2
    + Polynomial.C ((66 : ℤ) : ℚ) * X + Polynomial.C ((106 : ℤ) : ℚ) :=
  (minpoly.eq_of_irreducible_of_monic hirr.out Adj.aeval_root_self
    (T_monic.map (algebraMap ℤ ℚ))).symm.trans (by
      rw [T_map_eq, Polynomial.C_1, one_mul]
      push_cast
      ring)

/-- `θ` is the second element of the integral basis `1, θ, (θ² + 2θ + 1)/3`. -/
lemma theta_eq_basis : (⟨θ, hroot_mem⟩ : O) = B 1 :=
  BQ.root_eq_basis_one hroot_mem (by
    simp [BQ, List.ofFn_succ, ofList_cons, ofList_nil, map_ofNat, mul_comm])

/-! ### The three coordinate functionals -/

/-- The first coordinate, `nu 1 = 1` and `nu θ = 0`. -/
abbrev nu : O →ₗ[ℤ] ℤ := muOfBasis timesTableO.basis ![1, 0, 0]

/-- The second coordinate, `la 1 = 0` and `la θ = 1`. -/
abbrev la : O →ₗ[ℤ] ℤ := muOfBasis timesTableO.basis ![0, 1, 0]

lemma nu_one : nu 1 = 1 := by
  have h : nu (B 0) = (![1, 0, 0] : Fin 3 → ℤ) 0 :=
    muOfBasis_basis (b := timesTableO.basis) ![1, 0, 0] 0
  rwa [B_one] at h

lemma la_one : la 1 = 0 := by
  have h : la (B 0) = (![0, 1, 0] : Fin 3 → ℤ) 0 :=
    muOfBasis_basis (b := timesTableO.basis) ![0, 1, 0] 0
  rwa [B_one] at h

lemma mu_theta : mu ⟨θ, hroot_mem⟩ = 0 := by
  rw [theta_eq_basis]; exact muOfBasis_basis kMu 1

lemma nu_theta : nu ⟨θ, hroot_mem⟩ = 0 := by
  rw [theta_eq_basis]; exact muOfBasis_basis (b := timesTableO.basis) ![1, 0, 0] 1

lemma la_theta : la ⟨θ, hroot_mem⟩ = 1 := by
  rw [theta_eq_basis]; exact muOfBasis_basis (b := timesTableO.basis) ![0, 1, 0] 1

lemma hZ1 : (Z1 : O) = zeta1 := Subtype.ext Z1_coe

/-! ### The Skolem step -/

theorem mu_Z1_zpow_eq_zero_iff (n : ℤ) : mu ((Z1 ^ n : Oˣ) : O) = 0 ↔ n ∈ [(0 : ℤ)] := by
  obtain ⟨δ, hS1, hS2, hW0⟩ := zeta1_pow_12
  refine skolem_zpow_eq_zero_iff_mem mu Z1 (p := pS) (f := 12) (by norm_num) (by norm_num)
    (by norm_num) δ ?_ [(0 : ℤ)] ?_ ?_ ?_ n
  · rw [Units.val_pow_eq_pow_val, hZ1]; exact hS1
  · intro r hr hne
    rw [hZ1]
    exact not_dvd_mu_zeta1_pow r hr (by have := hne (0) (by simp); omega)
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    · simpa using mu_one
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    · rw [hZ1]; exact (by decide : ((0 : ℤ) % (12 : ℤ)).toNat = 0) ▸ hW0

/-! ### The Thue equation -/

/-- **The Thue equation `A ^ 3 + 15 * A ^ 2 * B + 66 * A * B ^ 2 + 106 * B ^ 3 = 1`.** -/
theorem thue_eq_one_iff_3_1_1704_1 (A B' : ℤ) :
    A ^ 3 + 15 * A ^ 2 * B' + 66 * A * B' ^ 2 + 106 * B' ^ 3 = 1 ↔ (A = 1 ∧ B' = 0) := by
  obtain ⟨σ, hσ⟩ := exists_not_isReal_K
  refine ⟨fun hF => ?_, by rintro ⟨rfl, rfl⟩ <;> ring⟩
  obtain ⟨n, hmun, hA, hB⟩ := exists_zpow_eq_coeffs_of_thue K_finrank σ _
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign) hσ
    hroot_mem minpoly_root Z1 (by rw [Z1_coe]; exact zeta1_embedding_one_lt) units_eq_zpow_Z1
    mu mu_one mu_theta nu nu_one nu_theta la la_one la_theta
    (a := A) (b := B') (by linear_combination hF)
  have hn := (mu_Z1_zpow_eq_zero_iff n).mp hmun
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · rw [zpow_zero, Units.val_one] at hA hB
    exact ⟨hA.trans nu_one, hB.trans (neg_eq_zero.mpr la_one)⟩

end

end NF3_1_1704_1
