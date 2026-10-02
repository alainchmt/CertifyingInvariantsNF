import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.FundamentalUnit3_1_24312_1
import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.UnitPowMod3_1_24312_1

/-!
# `A³ + 3AB² - 90B³ = 1` has only the solution `(1, 0)`

This is the Thue equation attached to `y² = x³ + 2026`.  The file is pure assembly:
`exists_zpow_eq_coeffs_of_thue` and `skolem_zpow_eq_zero_iff_mem` are fed with

* the field data of `NF3_1_24312_1` (`K_finrank`, `exists_not_isReal_K`, `T_map_eq`);
* the fundamental unit `Z1` and `units_eq_zpow_Z1` (Artin, `FundamentalUnit`), with
  `zeta1_embedding_one_lt` (`EmbeddingApprox`);
* the Skolem certificate at `p = 83`, `f = 82` (`UnitPowMod`).

The only new content concerns `θ = Adj.root`, the root adjoined to define `K`:
`minpoly_root` is its minimal polynomial (it is a root of the monic irreducible `T`), and
`theta_eq_basis` identifies it with the second element of the integral basis, whence
`mu θ = 0`.

Opus 5
-/

set_option linter.all false

open Module Polynomial NumberField NumberField.ComplexEmbedding

local notation "θ" => Adj.root

/-- The minimal polynomial of `θ` is the defining cubic `X³ + 3X - 90`. -/
lemma minpoly_root : minpoly ℚ θ
    = X ^ 3 + C ((0 : ℤ) : ℚ) * X ^ 2 + C ((3 : ℤ) : ℚ) * X + C (((-90) : ℤ) : ℚ) := by
  rw [(minpoly.eq_of_irreducible_of_monic hirr.out (Adj.aeval_root_self)
    (T_monic.map (algebraMap ℤ ℚ))).symm, T_map_eq, map_one, one_mul]
  push_cast
  ring

/-- `θ` is the second element `B 1` of the integral basis `1, θ, θ²/3`. -/
lemma theta_eq_basis : (⟨θ, hroot_mem⟩ : O) = B 1 := by
  apply Subtype.ext
  show θ = ((basisOfBuilderLists T [-90, 3, 0, 1] BQ) 1 : O)
  rw [basisOfBuilderLists_apply, ← Adj.map_X]
  congr 1
  simp [BQ, ofList_cons, ofList_nil]
  have h3 : (C (3⁻¹ : ℚ)) * 3 = 1 := by
    rw [show (3 : ℚ[X]) = C 3 from (map_ofNat Polynomial.C 3).symm, ← Polynomial.C_mul]
    norm_num
  linear_combination (-X) * h3

/-- Hence `mu θ = 0`: the `θ²/3`-coordinate of `B 1` vanishes. -/
lemma mu_theta : mu ⟨θ, hroot_mem⟩ = 0 := by
  rw [theta_eq_basis]
  exact muOfBasis_basis kMu 1

/-! ### The other two coordinate functionals -/

/-- The first coordinate, `nu 1 = 1` and `nu θ = 0`. -/
noncomputable abbrev nu : O →ₗ[ℤ] ℤ := muOfBasis timesTableO.basis ![1, 0, 0]

/-- The second coordinate, `la 1 = 0` and `la θ = 1`. -/
noncomputable abbrev la : O →ₗ[ℤ] ℤ := muOfBasis timesTableO.basis ![0, 1, 0]

lemma nu_one : nu 1 = 1 := by
  have h : nu (B 0) = (![1, 0, 0] : Fin 3 → ℤ) 0 :=
    muOfBasis_basis (b := timesTableO.basis) ![1, 0, 0] 0
  rwa [B_one] at h

lemma la_one : la 1 = 0 := by
  have h : la (B 0) = (![0, 1, 0] : Fin 3 → ℤ) 0 :=
    muOfBasis_basis (b := timesTableO.basis) ![0, 1, 0] 0
  rwa [B_one] at h

lemma nu_theta : nu ⟨θ, hroot_mem⟩ = 0 := by
  rw [theta_eq_basis]
  exact muOfBasis_basis (b := timesTableO.basis) ![1, 0, 0] 1

lemma la_theta : la ⟨θ, hroot_mem⟩ = 1 := by
  rw [theta_eq_basis]
  exact muOfBasis_basis (b := timesTableO.basis) ![0, 1, 0] 1

lemma hZ1 : (Z1 : O) = zeta1 := Subtype.ext Z1_coe

/-! ### The Skolem step -/

theorem mu_Z1_zpow_eq_zero_iff (n : ℤ) : mu ((Z1 ^ n : Oˣ) : O) = 0 ↔ n ∈ [(0 : ℤ)] := by
  obtain ⟨δ, hS1, hS2⟩ := zeta1_pow_82
  refine skolem_zpow_eq_zero_iff_mem mu Z1 (p := 83) (f := 82) (by norm_num) (by norm_num)
    (by norm_num) δ ?_ [(0 : ℤ)] ?_ ?_ ?_ n
  · rw [Units.val_pow_eq_pow_val, hZ1]; exact hS1
  · intro r hr hne
    rw [hZ1]
    exact not_dvd_mu_zeta1_pow r (by have := hne 0 (by simp); omega) hr
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    · simpa using mu_one
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl
    · simpa using hS2

/-! ### The Thue equation -/

/-- **The Thue equation attached to `y² = x³ + 2026`.** -/
theorem thue_eq_one_iff_3_1_24312_1 (A B : ℤ) :
    A ^ 3 + 3 * A * B ^ 2 - 90 * B ^ 3 = 1 ↔ (A = 1 ∧ B = 0) := by
  obtain ⟨σ, hσ⟩ := exists_not_isReal_K
  refine ⟨fun hF => ?_, by rintro ⟨rfl, rfl⟩ <;> ring⟩
  obtain ⟨n, hmun, hA, hB⟩ := exists_zpow_eq_coeffs_of_thue K_finrank σ _
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign) hσ
    hroot_mem minpoly_root Z1 (by rw [Z1_coe]; exact zeta1_embedding_one_lt) units_eq_zpow_Z1
    mu mu_one mu_theta nu nu_one nu_theta la la_one la_theta
    (a := A) (b := B) (by linear_combination hF)
  have hn := (mu_Z1_zpow_eq_zero_iff n).mp hmun
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl
  · rw [zpow_zero, Units.val_one] at hA hB
    exact ⟨hA.trans nu_one, hB.trans (neg_eq_zero.mpr la_one)⟩
