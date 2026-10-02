import IdealArithmetic.MordellExamples.MordellExample142.NF2_2_568_1.ClassGroupRepresentatives

/-!
# `y ^ 2 = x ^ 3 + 142` reduces to two Thue equations

The case **`3 ∣ h`**: here `142 ≡ 2 [ZMOD 4]`, so
`O = ℤ[√142]` is the full ring of integers and `x` is odd, but the class group is `ℤ/3`, so the
ideal `(y + √142) = D ^ 3` need not have `D` principal.

`Mordell.exists_unit_mul_cube_of_mordell_rep_int` supplies the replacement: with `J0 = (3, 2+√142)`
the prime above `3` and `J0 ^ 3 = (alpha0)`, `alpha0 = -13 + √142`, every ideal is made principal
by one of `1, J0, J0 ^ 2` (`class_group_covers_O`), and the descent becomes

  `alpha0 ^ j · (y + √142) = zeta1 ^ e · γ ^ 3`,   `j, e ∈ {0, 1, 2}`,  `γ ∈ O`.

The multiplier sits on the **left**, so eliminating `y` from the coefficient match gives a Thue
equation with right-hand side `-N(alpha0 ^ j) = -27 ^ j`, not `1`.  The cube is divided out by
the congruences the equation itself forces: `27 ^ j ∣` the form exactly on the sublattice
`γ ∈ J0 ^ j`, and that sublattice condition is implied modulo `3` by the equation.  One
substitution per power of `27` brings every right-hand side back to `±1`.

Of the nine `(j, e)` pairs: `(0,0)` is degenerate, the six with `e ≠ 0` are insoluble mod `9`,
and `(1,0)`, `(2,0)` give the two Thue equations below -- both over the cubic field of
discriminant `-1704`, and each with the single solution `(1,0)`, giving `x = 3`.

Opus 5
-/

set_option linter.all false

open Mordell Polynomial NumberField NF2_2_568_1

attribute [local instance 10000] CommRing.toCommSemiring CommRing.toRing

noncomputable section

/-! ### `√142` inside `O` -/

/-- `√142`, the second vector of the integral basis. -/
def sd : O := B.equivFun.symm ![0, 1]

lemma sd_sq : sd ^ 2 = 142 := by
  have h : aeval (timesTableO.basis.equivFun.symm ![0, 1]) (ofList [(-142 : ℤ), 0, 1]) = 0 := by
    rw [← minpoly_hroot]; exact minpoly.aeval ℤ _
  rw [T_ofList, T_def] at h
  simp only [map_sub, map_pow, aeval_X, map_ofNat] at h
  exact eq_of_sub_eq_zero h

lemma sd_sq' : sd ^ 2 = ((142 : ℤ) : O) := by push_cast; exact sd_sq

lemma zsmulOne (n : ℤ) : n • (1 : O) = (n : O) := by simp

lemma zsmul_eq (n : ℤ) (z : O) : n • z = (n : O) * z :=
  (Algebra.smul_def n z).trans (congrArg (· * z) (eq_intCast (algebraMap ℤ O) n))

lemma sd_eq_B1 : sd = B 1 := by
  show B.equivFun.symm ![0, 1] = B 1
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zero_smul]
  exact (zero_add _).trans (one_smul ℤ (B 1))

lemma coord_eq (p q : ℤ) : B.equivFun.symm ![p, q] = (p : O) + (q : O) * sd := by
  rw [Module.Basis.equivFun_symm_apply, Fin.sum_univ_two, sd_eq_B1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  congr 1
  · rw [B_one]; exact zsmulOne p
  · exact zsmul_eq q (B 1)

lemma exists_coords (δ : O) : ∃ a b : ℤ, δ = (a : O) + (b : O) * sd := by
  refine ⟨B.equivFun δ 0, B.equivFun δ 1, ?_⟩
  rw [← coord_eq]
  conv_lhs => rw [← B.equivFun.symm_apply_apply δ]
  congr 1
  ext i
  fin_cases i <;> rfl

lemma coords_inj {p q r s : ℤ} (hc : (p : O) + (q : O) * sd = (r : O) + (s : O) * sd) :
    p = r ∧ q = s := by
  rw [← coord_eq, ← coord_eq] at hc
  have h2 := B.equivFun.symm.injective hc
  exact ⟨congrFun h2 0, congrFun h2 1⟩

lemma ne_zero_of_add_sd (y : ℤ) : ((y : O) + sd) ≠ 0 := by
  intro h0
  refine one_ne_zero (coords_inj (p := y) (q := 1) (r := 0) (s := 0) ?_).2
  push_cast
  rw [one_mul, zero_mul, add_zero]
  exact h0

/-! ### Expansions in the basis `1, √142` -/

lemma cube_expand (a b : ℤ) :
    ((a : O) + (b : O) * sd) ^ 3
      = ((a ^ 3 + 426 * a * b ^ 2 : ℤ) : O) + ((3 * a ^ 2 * b + 142 * b ^ 3 : ℤ) : O) * sd := by
  push_cast
  linear_combination ((b : O) ^ 3 * sd + 3 * (a : O) * (b : O) ^ 2) * sd_sq

/-- `zeta1 = 143 + 12√142` is the fundamental unit. -/
lemma zeta1_coords : zeta1 = ((143 : ℤ) : O) + ((12 : ℤ) : O) * sd := by
  show B.equivFun.symm ![143, 12] = _
  rw [coord_eq]

lemma mul_zeta1_expand (P Q : ℤ) :
    zeta1 * (((P : ℤ) : O) + ((Q : ℤ) : O) * sd)
      = ((143 * P + 1704 * Q : ℤ) : O) + ((12 * P + 143 * Q : ℤ) : O) * sd := by
  rw [zeta1_coords]
  push_cast
  linear_combination (12 * (Q : O)) * sd_sq

/-- `alpha0 = -13 + √142`, the generator of `J0 ^ 3`. -/
lemma alpha0_coords : alpha0 = ((-13 : ℤ) : O) + ((1 : ℤ) : O) * sd := by
  show B.equivFun.symm ![-13, 1] = _
  rw [coord_eq]

lemma alpha0_sq_mul (y : ℤ) : alpha0 ^ 2 * ((y : O) + sd)
    = (((311 * y - 3692 : ℤ)) : O) + (((-26 * y + 311 : ℤ)) : O) * sd := by
  rw [alpha0_coords]; push_cast; linear_combination ((y : O) + sd - 26) * sd_sq

/-! ### Arithmetic input -/

lemma hsqfree : Squarefree (142 : ℤ) := Int.squarefree_natCast.mpr (by decide +kernel)

/-! ### The descent -/

/-- `j = 0`: the multiplier is trivial.  `e = 0` is degenerate and `e = 1, 2` are insoluble mod `9`. -/
lemma branch_zero {x y a b : ℤ} (h : y ^ 2 = x ^ 3 + 142)
    (e : Fin 3) (hmain : ((y : O) + sd)
      = zeta1 ^ (e : ℕ) * (((a : ℤ) : O) + ((b : ℤ) : O) * sd) ^ 3) :
    False := by
  fin_cases e <;> norm_num at hmain
  · -- `j = 0`, `e = 0` : degenerate
    exfalso
    rw [show ((y : O) + sd) = (((y : ℤ)) : O) + (((1 : ℤ)) : O) * sd from by push_cast; ring,
      cube_expand] at hmain
    obtain ⟨-, hF⟩ := coords_inj hmain
    have hbd : (b : ℤ) ∣ 1 := ⟨3 * a ^ 2 + 142 * b ^ 2, by linear_combination hF⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hbd) with hb | hb <;> subst hb <;>
      nlinarith [sq_nonneg a, hF]
  · -- `j = 0`, `e = 1` : insoluble mod 9
    exfalso
    rw [show ((y : O) + sd) = (((y : ℤ)) : O) + (((1 : ℤ)) : O) * sd from by push_cast; ring,
      cube_expand, mul_zeta1_expand] at hmain
    obtain ⟨-, hF⟩ := coords_inj hmain
    have hz := congrArg (fun z : ℤ => (z : ZMod 9)) hF
    push_cast at hz
    revert hz
    generalize ((a : ZMod 9)) = A9
    generalize ((b : ZMod 9)) = B9
    revert A9 B9
    decide
  · -- `j = 0`, `e = 2` : insoluble mod 9
    exfalso
    rw [show ((y : O) + sd) = (((y : ℤ)) : O) + (((1 : ℤ)) : O) * sd from by push_cast; ring,
      cube_expand, sq, mul_assoc, mul_zeta1_expand, mul_zeta1_expand] at hmain
    obtain ⟨-, hF⟩ := coords_inj hmain
    have hz := congrArg (fun z : ℤ => (z : ZMod 9)) hF
    push_cast at hz
    revert hz
    generalize ((a : ZMod 9)) = A9
    generalize ((b : ZMod 9)) = B9
    revert A9 B9
    decide

/-- `j = 1`: multiplier `alpha0`, right-hand side `-27`; the equation forces `a ≡ 2b [ZMOD 3]`, and the substitution `a = 2b + 3c` divides it by `27`. -/
lemma branch_one {x y a b : ℤ} (h : y ^ 2 = x ^ 3 + 142)
    (e : Fin 3) (hmain : alpha0 * ((y : O) + sd)
      = zeta1 ^ (e : ℕ) * (((a : ℤ) : O) + ((b : ℤ) : O) * sd) ^ 3) :
    ∃ A B : ℤ, A ^ 3 + 15 * A ^ 2 * B + 66 * A * B ^ 2 + 106 * B ^ 3 = 1 ∧
      x = 3 * A ^ 2 + 4 * A * B - 46 * B ^ 2 := by
  fin_cases e <;> norm_num at hmain
  · -- `j = 1`, `e = 0` : the Thue equation `A³ + 15A²B + 66AB² + 106B³ = 1`
    rw [show alpha0 * ((y : O) + sd)
        = (((-13 * y + 142 : ℤ)) : O) + (((y - 13 : ℤ)) : O) * sd from by
      rw [alpha0_coords]; push_cast; linear_combination (1 : O) * sd_sq, cube_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj hmain
    have hT : (a ^ 3 + 39 * a ^ 2 * b + 426 * a * b ^ 2 + 1846 * b ^ 3 : ℤ) = -27 := by
      linear_combination -hG - 13 * hF
    have hx : (27 : ℤ) * x ^ 3 = (a ^ 2 - 142 * b ^ 2) ^ 3 := by
      linear_combination (-27) * h + (a ^ 3 + 426 * a * b ^ 2 - 13 * y + 142) * hG
        - 142 * (3 * a ^ 2 * b + 142 * b ^ 3 + y - 13) * hF
    obtain ⟨c, rfl⟩ : ∃ c : ℤ, a = 2 * b + 3 * c := by
      have h3 : (3 : ℤ) ∣ a - 2 * b := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_
        have hz := congrArg (fun z : ℤ => (z : ZMod 3)) hT
        push_cast at hz ⊢
        revert hz
        generalize ((a : ZMod 3)) = A3
        generalize ((b : ZMod 3)) = B3
        revert A3 B3
        decide
      obtain ⟨c, hc⟩ := h3
      exact ⟨c, by linarith⟩
    have hT2 : (c ^ 3 + 15 * c ^ 2 * b + 66 * c * b ^ 2 + 106 * b ^ 3 : ℤ) = -1 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT)
    have hx3 : x ^ 3 = (3 * c ^ 2 + 4 * c * b - 46 * b ^ 2) ^ 3 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hx)
    exact ⟨-c, -b, by linear_combination -hT2, by
      have := cube_inj hx3; linear_combination this⟩
  · -- `j = 1`, `e = 1` : insoluble mod 9
    exfalso
    rw [show alpha0 * ((y : O) + sd)
        = (((-13 * y + 142 : ℤ)) : O) + (((y - 13 : ℤ)) : O) * sd from by
      rw [alpha0_coords]; push_cast; linear_combination (1 : O) * sd_sq,
      cube_expand, mul_zeta1_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj hmain
    have hT : (299 * a ^ 3 + 10689 * a ^ 2 * b + 127374 * a * b ^ 2 + 505946 * b ^ 3 : ℤ) = -27 := by
      linear_combination -hG - 13 * hF
    obtain ⟨c, rfl⟩ : ∃ c : ℤ, a = 2 * b + 3 * c := by
      have h3 : (3 : ℤ) ∣ a - 2 * b := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_
        have hz := congrArg (fun z : ℤ => (z : ZMod 3)) hT
        push_cast at hz ⊢
        revert hz
        generalize ((a : ZMod 3)) = A3
        generalize ((b : ZMod 3)) = B3
        revert A3 B3
        decide
      obtain ⟨c, hc⟩ := h3
      exact ⟨c, by linarith⟩
    have hT2 : (299 * c ^ 3 + 4161 * c ^ 2 * b + 19302 * c * b ^ 2 + 29846 * b ^ 3 : ℤ) = -1 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT)
    have hz := congrArg (fun z : ℤ => (z : ZMod 9)) hT2
    push_cast at hz
    revert hz
    generalize ((c : ZMod 9)) = C9
    generalize ((b : ZMod 9)) = B9
    revert C9 B9
    decide
  · -- `j = 1`, `e = 2` : insoluble mod 9
    exfalso
    rw [show alpha0 * ((y : O) + sd)
        = (((-13 * y + 142 : ℤ)) : O) + (((y - 13 : ℤ)) : O) * sd from by
      rw [alpha0_coords]; push_cast; linear_combination (1 : O) * sd_sq,
      cube_expand, sq, mul_assoc, mul_zeta1_expand, mul_zeta1_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj hmain
    have hT : (85513 * a ^ 3 + 3057015 * a ^ 2 * b + 36428538 * a * b ^ 2
        + 144698710 * b ^ 3 : ℤ) = -27 := by linear_combination -hG - 13 * hF
    obtain ⟨c, rfl⟩ : ∃ c : ℤ, a = 2 * b + 3 * c := by
      have h3 : (3 : ℤ) ∣ a - 2 * b := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_
        have hz := congrArg (fun z : ℤ => (z : ZMod 3)) hT
        push_cast at hz ⊢
        revert hz
        generalize ((a : ZMod 3)) = A3
        generalize ((b : ZMod 3)) = B3
        revert A3 B3
        decide
      obtain ⟨c, hc⟩ := h3
      exact ⟨c, by linarith⟩
    have hT2 : (85513 * c ^ 3 + 1190031 * c ^ 2 * b + 5520306 * c * b ^ 2
        + 8535850 * b ^ 3 : ℤ) = -1 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT)
    have hz := congrArg (fun z : ℤ => (z : ZMod 9)) hT2
    push_cast at hz
    revert hz
    generalize ((c : ZMod 9)) = C9
    generalize ((b : ZMod 9)) = B9
    revert C9 B9
    decide

/-- `j = 2`: multiplier `alpha0 ^ 2`, right-hand side `-729`; two substitutions, each dividing by
`27`.  The resulting form is `GL₂(ℤ)`-equivalent to the one of `branch_one` via
`(A, B) ↦ (A + 5B, -B)`, so the conclusion is stated with the same Thue equation. -/
lemma branch_two {x y a b : ℤ} (h : y ^ 2 = x ^ 3 + 142)
    (e : Fin 3) (hmain : alpha0 ^ 2 * ((y : O) + sd)
      = zeta1 ^ (e : ℕ) * (((a : ℤ) : O) + ((b : ℤ) : O) * sd) ^ 3) :
    ∃ A B : ℤ, A ^ 3 + 15 * A ^ 2 * B + 66 * A * B ^ 2 + 106 * B ^ 3 = 1 ∧
      x = 3 * A ^ 2 + 4 * A * B - 46 * B ^ 2 := by
  fin_cases e <;> norm_num at hmain
  · -- `j = 2`, `e = 0` : the Thue equation `A³ - 9AB² - 26B³ = 1`
    have hm := (alpha0_sq_mul y).symm.trans hmain
    rw [cube_expand] at hm
    obtain ⟨hG, hF⟩ := coords_inj hm
    have hT : (-26 * a ^ 3 - 933 * a ^ 2 * b - 11076 * a * b ^ 2 - 44162 * b ^ 3 : ℤ) = -729 := by
      linear_combination 26 * hG + 311 * hF
    have hx : (729 : ℤ) * x ^ 3 = (a ^ 2 - 142 * b ^ 2) ^ 3 := by
      linear_combination (-729) * h + (a ^ 3 + 426 * a * b ^ 2 + 311 * y - 3692) * hG
        - 142 * (3 * a ^ 2 * b + 142 * b ^ 3 - 26 * y + 311) * hF
    obtain ⟨c, rfl⟩ : ∃ c : ℤ, a = 2 * b + 3 * c := by
      have h3 : (3 : ℤ) ∣ a - 2 * b := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_
        have hz := congrArg (fun z : ℤ => (z : ZMod 3)) hT
        push_cast at hz ⊢
        revert hz
        generalize ((a : ZMod 3)) = A3
        generalize ((b : ZMod 3)) = B3
        revert A3 B3
        decide
      obtain ⟨c, hc⟩ := h3
      exact ⟨c, by linarith⟩
    have hT2 : (-26 * c ^ 3 - 363 * c ^ 2 * b - 1680 * c * b ^ 2 - 2602 * b ^ 3 : ℤ) = -27 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT)
    obtain ⟨f, rfl⟩ : ∃ f : ℤ, c = b + 3 * f := by
      have h3 : (3 : ℤ) ∣ c - b := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_
        have hz := congrArg (fun z : ℤ => (z : ZMod 3)) hT2
        push_cast at hz ⊢
        revert hz
        generalize ((c : ZMod 3)) = C3
        generalize ((b : ZMod 3)) = B3
        revert C3 B3
        decide
      obtain ⟨f, hf⟩ := h3
      exact ⟨f, by linarith⟩
    have hT3 : (-26 * f ^ 3 - 147 * f ^ 2 * b - 276 * f * b ^ 2 - 173 * b ^ 3 : ℤ) = -1 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT2)
    have hx3 : x ^ 3 = (9 * f ^ 2 + 10 * f * b - 13 * b ^ 2) ^ 3 :=
      mul_left_cancel₀ (by norm_num : (729 : ℤ) ≠ 0) (by linear_combination hx)
    -- `(A, B) ↦ (A + 5B, -B)` identifies this equation with the one of `branch_one`
    exact ⟨-5 * f - 9 * b, f + 2 * b, by linear_combination -hT3, by
      have := cube_inj hx3; linear_combination this⟩
  · -- `j = 2`, `e = 1` : insoluble mod 9
    exfalso
    have hm := (alpha0_sq_mul y).symm.trans hmain
    rw [cube_expand, mul_zeta1_expand] at hm
    obtain ⟨hG, hF⟩ := coords_inj hm
    have hT : (-7450 * a ^ 3 - 266331 * a ^ 2 * b - 3173700 * a * b ^ 2
        - 12606334 * b ^ 3 : ℤ) = -729 := by linear_combination 26 * hG + 311 * hF
    obtain ⟨c, rfl⟩ : ∃ c : ℤ, a = 2 * b + 3 * c := by
      have h3 : (3 : ℤ) ∣ a - 2 * b := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_
        have hz := congrArg (fun z : ℤ => (z : ZMod 3)) hT
        push_cast at hz ⊢
        revert hz
        generalize ((a : ZMod 3)) = A3
        generalize ((b : ZMod 3)) = B3
        revert A3 B3
        decide
      obtain ⟨c, hc⟩ := h3
      exact ⟨c, by linarith⟩
    have hT2 : (-7450 * c ^ 3 - 103677 * c ^ 2 * b - 480936 * c * b ^ 2
        - 743654 * b ^ 3 : ℤ) = -27 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT)
    obtain ⟨f, rfl⟩ : ∃ f : ℤ, c = b + 3 * f := by
      have h3 : (3 : ℤ) ∣ c - b := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_
        have hz := congrArg (fun z : ℤ => (z : ZMod 3)) hT2
        push_cast at hz ⊢
        revert hz
        generalize ((c : ZMod 3)) = C3
        generalize ((b : ZMod 3)) = B3
        revert C3 B3
        decide
      obtain ⟨f, hf⟩ := h3
      exact ⟨f, by linarith⟩
    have hT3 : (-7450 * f ^ 3 - 42009 * f ^ 2 * b - 78960 * f * b ^ 2
        - 49471 * b ^ 3 : ℤ) = -1 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT2)
    have hz := congrArg (fun z : ℤ => (z : ZMod 9)) hT3
    push_cast at hz
    revert hz
    generalize ((f : ZMod 9)) = F9
    generalize ((b : ZMod 9)) = B9
    revert F9 B9
    decide
  · -- `j = 2`, `e = 2` : insoluble mod 9
    exfalso
    have hm := (alpha0_sq_mul y).symm.trans hmain
    rw [cube_expand, sq, mul_assoc, mul_zeta1_expand, mul_zeta1_expand] at hm
    obtain ⟨hG, hF⟩ := coords_inj hm
    have hT : (-2130674 * a ^ 3 - 76169733 * a ^ 2 * b - 907667124 * a * b ^ 2
        - 3605367362 * b ^ 3 : ℤ) = -729 := by linear_combination 26 * hG + 311 * hF
    obtain ⟨c, rfl⟩ : ∃ c : ℤ, a = 2 * b + 3 * c := by
      have h3 : (3 : ℤ) ∣ a - 2 * b := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_
        have hz := congrArg (fun z : ℤ => (z : ZMod 3)) hT
        push_cast at hz ⊢
        revert hz
        generalize ((a : ZMod 3)) = A3
        generalize ((b : ZMod 3)) = B3
        revert A3 B3
        decide
      obtain ⟨c, hc⟩ := h3
      exact ⟨c, by linarith⟩
    have hT2 : (-2130674 * c ^ 3 - 29651259 * c ^ 2 * b - 137546016 * c * b ^ 2
        - 212682442 * b ^ 3 : ℤ) = -27 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT)
    obtain ⟨f, rfl⟩ : ∃ f : ℤ, c = b + 3 * f := by
      have h3 : (3 : ℤ) ∣ c - b := by
        refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp ?_
        have hz := congrArg (fun z : ℤ => (z : ZMod 3)) hT2
        push_cast at hz ⊢
        revert hz
        generalize ((c : ZMod 3)) = C3
        generalize ((b : ZMod 3)) = B3
        revert C3 B3
        decide
      obtain ⟨f, hf⟩ := h3
      exact ⟨f, by linarith⟩
    have hT3 : (-2130674 * f ^ 3 - 12014427 * f ^ 2 * b - 22582284 * f * b ^ 2
        - 14148533 * b ^ 3 : ℤ) = -1 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT2)
    have hz := congrArg (fun z : ℤ => (z : ZMod 9)) hT3
    push_cast at hz
    revert hz
    generalize ((f : ZMod 9)) = F9
    generalize ((b : ZMod 9)) = B9
    revert F9 B9
    decide

/-- **Mordell implies Thue for `d = 142`.**

The nine `(j, e)` branches collapse to a single Thue equation: `(0,0)` is degenerate, the six
with `e ≠ 0` are insoluble mod `9`, and the two survivors `(1,0)` and `(2,0)` give forms that
are `GL₂(ℤ)`-equivalent (via `(A,B) ↦ (A + 5B, -B)`, which also matches the two formulas for
`x`).  The cubic is the norm form of `θ` with `θ³ + 15θ² + 66θ + 106 = 0`, a generator of the
field of discriminant `-1704` and class number `1`. -/
theorem mordell142_imp_thue {x y : ℤ} (h : y ^ 2 = x ^ 3 + 142) :
    ∃ A B : ℤ, A ^ 3 + 15 * A ^ 2 * B + 66 * A * B ^ 2 + 106 * B ^ 3 = 1 ∧
      x = 3 * A ^ 2 + 4 * A * B - 46 * B ^ 2 := by
  obtain ⟨j, u, δ, hj⟩ := exists_unit_mul_cube_of_mordell_rep_int sd_sq' h
    (isCoprime_two_mul hsqfree h (not_two_dvd_of_mordell (by decide) h))
    (ne_zero_of_add_sd y) (A := fun j : Fin 3 => J0 ^ (j : ℕ))
    (α := fun j : Fin 3 => alpha0 ^ (j : ℕ)) (fun _ => Submonoid.pow_mem _ J0_mem _)
    (fun j => J0_pow_cube (j : ℕ)) class_group_covers_O
  obtain ⟨e, t, ht⟩ := units_eq_zeta1_pow_mul_cube u
  obtain ⟨a, b, hab⟩ := exists_coords ((t : O) * δ)
  have hmain : alpha0 ^ (j : ℕ) * ((y : O) + sd)
      = zeta1 ^ (e : ℕ) * (((a : ℤ) : O) + ((b : ℤ) : O) * sd) ^ 3 := by
    rw [← hab, hj, ht]; ring
  fin_cases j <;> norm_num at hmain
  · exact absurd hmain (fun hc => branch_zero h e hc)
  · exact branch_one h e hmain
  · exact branch_two h e hmain

end
