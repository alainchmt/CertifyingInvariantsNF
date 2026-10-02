import IdealArithmetic.MordellExamples.MordellExample17.NF3_1_1836_1.FundamentalUnit3_1_1836_1
import IdealArithmetic.MordellExamples.MordellExample17.NF3_1_1836_1.UnitPowMod3_1_1836_1
import IdealArithmetic.ConductorSubalgebraBuilder
import IdealArithmetic.MordellThueProject.PolyApprox

/-!
# `A ^ 3 - 6 * A * B' ^ 2 - 10 * B' ^ 3 = 1` has exactly 2 solutions

The Thue equation attached to the `x`-even, `e = 0` branch of `y² = x³ + 17`.
The Skolem certificate is at `p = 349`, `f = 116`; the two surviving residue classes `0` and
`115` hold the two solutions `n = 0` and `n = -1`, each pinned down by the re-centering
hypothesis `349 ∤ mu (zeta1 ^ r δ)`.

Opus 5
-/

set_option linter.all false

open Module Polynomial NumberField NumberField.ComplexEmbedding

namespace NF3_1_1836_1

noncomputable section

local notation "θ" => Adj.root

/-- The minimal polynomial of `θ` is the defining cubic. -/
lemma minpoly_root : minpoly ℚ θ = X ^ 3 + Polynomial.C ((0 : ℤ) : ℚ) * X ^ 2
    + Polynomial.C ((-6 : ℤ) : ℚ) * X + Polynomial.C (((-10) : ℤ) : ℚ) :=
  (minpoly.eq_of_irreducible_of_monic hirr.out Adj.aeval_root_self
    (T_monic.map (algebraMap ℤ ℚ))).symm.trans (by
      rw [T_map_eq, Polynomial.C_1, one_mul]
      push_cast
      ring)

/-- `θ` is the second element of the integral basis `1, θ, θ²`. -/
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

/-- A coordinate functional evaluated on an element given by its coordinate vector. -/
lemma coord_apply (k v : Fin 3 → ℤ) :
    muOfBasis timesTableO.basis k (B.equivFun.symm v) = ∑ i, k i * v i :=
  muOfBasis_symm (b := timesTableO.basis) k v

lemma mu_theta : mu ⟨θ, hroot_mem⟩ = 0 := by
  rw [theta_eq_basis]; exact muOfBasis_basis kMu 1

lemma nu_theta : nu ⟨θ, hroot_mem⟩ = 0 := by
  rw [theta_eq_basis]; exact muOfBasis_basis (b := timesTableO.basis) ![1, 0, 0] 1

lemma la_theta : la ⟨θ, hroot_mem⟩ = 1 := by
  rw [theta_eq_basis]; exact muOfBasis_basis (b := timesTableO.basis) ![0, 1, 0] 1

/-! ### Negative powers of the fundamental unit -/

lemma hZ1 : (Z1 : O) = zeta1 := Subtype.ext Z1_coe

lemma zeta1_mul_inv : zeta1 * (B.equivFun.symm ![-3, 1, 0]) = 1 := by
  rw [show (1 : O) = B.equivFun.symm ![1, 0, 0] from B_one_repr.symm]
  refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
  rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
  decide

lemma inv_coord : ((Z1 ^ (-1 : ℤ) : Oˣ) : O) = B.equivFun.symm ![-3, 1, 0] := by
  rw [zpow_neg_one]
  exact Units.inv_eq_of_mul_eq_one_right (by rw [hZ1]; exact zeta1_mul_inv)

/-! ### The Skolem step -/

theorem mu_Z1_zpow_eq_zero_iff (n : ℤ) : mu ((Z1 ^ n : Oˣ) : O) = 0 ↔ n ∈ [(0 : ℤ), -1] := by
  obtain ⟨δ, hS1, hS2, hW0, hW115⟩ := zeta1_pow_116
  refine skolem_zpow_eq_zero_iff_mem mu Z1 (p := pS) (f := 116) (by norm_num) (by norm_num)
    (by norm_num) δ ?_ [(0 : ℤ), -1] ?_ ?_ ?_ n
  · rw [Units.val_pow_eq_pow_val, hZ1]; exact hS1
  · intro r hr hne
    rw [hZ1]
    exact not_dvd_mu_zeta1_pow r hr
      (by have := hne (0) (by simp); omega)
      (by have := hne (-1) (by simp); omega)
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · simpa using mu_one
    · rw [inv_coord, coord_apply]; decide
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · rw [hZ1]; exact (by decide : ((0 : ℤ) % (116 : ℤ)).toNat = 0) ▸ hW0
    · rw [hZ1]; exact (by decide : ((-1 : ℤ) % (116 : ℤ)).toNat = 115) ▸ hW115

/-! ### The Thue equation -/

/-- **The Thue equation `A ^ 3 - 6 * A * B' ^ 2 - 10 * B' ^ 3 = 1`.** -/
theorem thue_eq_one_iff_3_1_1836_1 (A B' : ℤ) :
    A ^ 3 - 6 * A * B' ^ 2 - 10 * B' ^ 3 = 1 ↔ (A = 1 ∧ B' = 0) ∨ (A = -3 ∧ B' = -1) := by
  obtain ⟨σ, hσ⟩ := exists_not_isReal_K
  refine ⟨fun hF => ?_, by rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ring⟩
  obtain ⟨n, hmun, hA, hB⟩ := exists_zpow_eq_coeffs_of_thue K_finrank σ _
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign) hσ
    hroot_mem minpoly_root Z1 (by rw [Z1_coe]; exact zeta1_embedding_one_lt) units_eq_zpow_Z1
    mu mu_one mu_theta nu nu_one nu_theta la la_one la_theta
    (a := A) (b := B') (by linear_combination hF)
  have hnu1 : nu ((Z1 ^ (-1 : ℤ) : Oˣ) : O) = -3 := by
    rw [inv_coord, coord_apply]; decide
  have hla1 : la ((Z1 ^ (-1 : ℤ) : Oˣ) : O) = 1 := by
    rw [inv_coord, coord_apply]; decide
  have hn := (mu_Z1_zpow_eq_zero_iff n).mp hmun
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl
  · rw [zpow_zero, Units.val_one] at hA hB
    exact Or.inl ⟨hA.trans nu_one, hB.trans (neg_eq_zero.mpr la_one)⟩
  · exact Or.inr ⟨hA.trans hnu1, hB.trans (congrArg Neg.neg hla1)⟩

end

end NF3_1_1836_1
