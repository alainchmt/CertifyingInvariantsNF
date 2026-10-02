import IdealArithmetic.MordellExamples.MordellExample17.NF3_1_459_1.FundamentalUnit3_1_459_1
import IdealArithmetic.MordellExamples.MordellExample17.NF3_1_459_1.UnitPowMod3_1_459_1
import IdealArithmetic.ConductorSubalgebraBuilder
import IdealArithmetic.MordellThueProject.PolyApprox

/-!
# `A³ + 3AB² - 8B³ = 1` has exactly the solutions `(1, 0)` and `(-3, -2)`

The Thue equation attached to the `x`-odd branch of `y² = x³ + 17`.  Assembly of

* the field data of `NF3_1_459_1` (`K_finrank`, `exists_not_isReal_K`, `T_map_eq`);
* the fundamental unit `Z1` with `units_eq_zpow_Z1` (Artin) and
  `zeta1_embedding_one_lt`;
* the Skolem certificate at `p = 11`, `f = 10` (`UnitPowMod`), whose two surviving residue
  classes `0` and `9` hold the two solutions `n = 0` and `n = -1`.

Two solutions rather than one, so `skolem_zpow_eq_zero_iff_mem` is used in place of
`skolem_zpow_eq_zero_iff`: the class of `9` is pinned down by the re-centering hypothesis
`11 ∤ mu (zeta1 ^ 9 δ)`.

Opus 5
-/

set_option linter.all false

open Module Polynomial NumberField NumberField.ComplexEmbedding

namespace NF3_1_459_1

noncomputable section

local notation "θ" => Adj.root

/-- The minimal polynomial of `θ` is the defining cubic `X³ + 3X - 8`. -/
lemma minpoly_root : minpoly ℚ θ = X ^ 3 + Polynomial.C ((0 : ℤ) : ℚ) * X ^ 2
    + Polynomial.C ((3 : ℤ) : ℚ) * X + Polynomial.C (((-8) : ℤ) : ℚ) :=
  (minpoly.eq_of_irreducible_of_monic hirr.out Adj.aeval_root_self
    (T_monic.map (algebraMap ℤ ℚ))).symm.trans (by
      rw [T_map_eq, Polynomial.C_1, one_mul]
      push_cast
      ring)

/-- `θ` is the second element of the integral basis `1, θ, (θ²+θ)/2`. -/
lemma theta_eq_basis : (⟨θ, hroot_mem⟩ : O) = B 1 :=
  BQ.root_eq_basis_one hroot_mem (by
    simp [BQ, List.ofFn_succ, ofList_cons, ofList_nil, map_ofNat]
    ring)

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

/-- `mu`, `nu`, `la` evaluated on an element given by its coordinate vector. -/
lemma coord_apply (k v : Fin 3 → ℤ) :
    muOfBasis timesTableO.basis k (B.equivFun.symm v) = ∑ i, k i * v i :=
  muOfBasis_symm (b := timesTableO.basis) k v

lemma mu_theta : mu ⟨θ, hroot_mem⟩ = 0 := by
  rw [theta_eq_basis]; exact muOfBasis_basis kMu 1

lemma nu_theta : nu ⟨θ, hroot_mem⟩ = 0 := by
  rw [theta_eq_basis]; exact muOfBasis_basis (b := timesTableO.basis) ![1, 0, 0] 1

lemma la_theta : la ⟨θ, hroot_mem⟩ = 1 := by
  rw [theta_eq_basis]; exact muOfBasis_basis (b := timesTableO.basis) ![0, 1, 0] 1

/-! ### The inverse of the fundamental unit -/

lemma hZ1 : (Z1 : O) = zeta1 := Subtype.ext Z1_coe

lemma zeta1_mul_inv : zeta1 * (B.equivFun.symm ![-3, 2, 0]) = 1 := by
  rw [show (1 : O) = B.equivFun.symm ![1, 0, 0] from B_one_repr.symm]
  refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
  rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
  decide

lemma Z1_zpow_neg_one : ((Z1 ^ (-1 : ℤ) : Oˣ) : O) = B.equivFun.symm ![-3, 2, 0] := by
  rw [zpow_neg_one]
  exact Units.inv_eq_of_mul_eq_one_right (by rw [hZ1]; exact zeta1_mul_inv)

/-! ### The Skolem step: `mu (Z1 ^ n) = 0` exactly for `n ∈ {0, -1}` -/

theorem mu_Z1_zpow_eq_zero_iff (n : ℤ) : mu ((Z1 ^ n : Oˣ) : O) = 0 ↔ n ∈ [(0 : ℤ), -1] := by
  obtain ⟨δ, hS1, hS2, hW0, hW9⟩ := zeta1_pow_10
  refine skolem_zpow_eq_zero_iff_mem mu Z1 (p := pS) (f := 10) (by norm_num) (by norm_num)
    (by norm_num) δ ?_ [(0 : ℤ), -1] ?_ ?_ ?_ n
  · rw [Units.val_pow_eq_pow_val, hZ1]; exact hS1
  · intro r hr hne
    rw [hZ1]
    exact not_dvd_mu_zeta1_pow r hr (by have := hne 0 (by simp); omega)
      (by have := hne (-1) (by simp); omega)
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · simpa using mu_one
    · rw [List.mem_singleton.mp hs, Z1_zpow_neg_one, coord_apply]
      decide
  · intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · rw [hZ1]; exact (by norm_num : ((0 : ℤ) % (10 : ℤ)).toNat = 0) ▸ hW0
    · rw [List.mem_singleton.mp hs, hZ1]
      exact (by decide : (((-1 : ℤ)) % (10 : ℤ)).toNat = 9) ▸ hW9

/-! ### The Thue equation -/

/-- **The Thue equation of the `x`-odd branch.** -/
theorem thue_eq_one_iff_3_1_459_1 (A B' : ℤ) :
    A ^ 3 + 3 * A * B' ^ 2 - 8 * B' ^ 3 = 1 ↔ (A = 1 ∧ B' = 0) ∨ (A = -3 ∧ B' = -2) := by
  obtain ⟨σ, hσ⟩ := exists_not_isReal_K
  refine ⟨fun hF => ?_, by rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ring⟩
  obtain ⟨n, hmun, hA, hB⟩ := exists_zpow_eq_coeffs_of_thue K_finrank σ _
    (realEmbeddingOfRealRootCubic_isReal hε_pos T_map_eq Adj hroot_sign) hσ
    hroot_mem minpoly_root Z1 (by rw [Z1_coe]; exact zeta1_embedding_one_lt) units_eq_zpow_Z1
    mu mu_one mu_theta nu nu_one nu_theta la la_one la_theta
    (a := A) (b := B') (by linear_combination hF)
  have hnu : nu ((Z1 ^ (-1 : ℤ) : Oˣ) : O) = -3 := by rw [Z1_zpow_neg_one, coord_apply]; decide
  have hla : la ((Z1 ^ (-1 : ℤ) : Oˣ) : O) = 2 := by rw [Z1_zpow_neg_one, coord_apply]; decide
  rcases List.mem_cons.mp ((mu_Z1_zpow_eq_zero_iff n).mp hmun) with rfl | hn
  · rw [zpow_zero, Units.val_one] at hA hB
    exact Or.inl ⟨hA.trans nu_one, hB.trans (neg_eq_zero.mpr la_one)⟩
  · rw [List.mem_singleton.mp hn] at hA hB
    exact Or.inr ⟨hA.trans hnu, hB.trans (congrArg Neg.neg hla)⟩

end

end NF3_1_459_1
