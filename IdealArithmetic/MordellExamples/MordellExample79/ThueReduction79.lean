import IdealArithmetic.MordellExamples.MordellExample79.NF2_2_316_1.ClassGroupRepresentatives

/-!
# `y ^ 2 = x ^ 3 + 79` reduces to a single Thue equation

The case **`3 ∣ h`**: here `79 ≡ 3 [ZMOD 4]`, so
`O = ℤ[√79]` is the full ring of integers and `x` is odd, but the class group is `ℤ/3`, so the
ideal `(y + √79) = D ^ 3` need not have `D` principal.  `d = 79` is the **smallest** `d > 1`
for which this happens.

`Mordell.exists_unit_mul_cube_of_mordell_rep_int` supplies the replacement: with `J0 = (3, 2+√79)`
the prime above `3` and `J0 ^ 3 = (alpha0)`, `alpha0 = -17 + 2√79` of norm `-27`, every ideal
is made principal by one of `1, J0, J0 ^ 2` (`class_group_covers_O`), and the descent
becomes

  `alpha0 ^ j · (y + √79) = zeta1 ^ e · γ ^ 3`,   `j, e ∈ {0, 1, 2}`,  `γ ∈ O`.

Of the nine `(j, e)` pairs: `(0,0)` is degenerate, **all six with `j ≠ 0` are insoluble mod
`9`**, and `(0,1)`, `(0,2)` give forms that are `GL₂(ℤ)`-equivalent, with the same formula for
`x`.  So the reduction ends at one equation.

This is the mirror image of `d = 142`, where the live branches were `j = 1, 2` and the `j = 0`
ones died.  Here the survivors have `j = 0`, so the right-hand side is already `1` and **no
sublattice substitution is needed on the live branches**; the `27`-clearing substitutions occur
only on branches that are then killed modulo `9`.

Opus 5
-/

set_option linter.all false

open Mordell Polynomial NumberField NF2_2_316_1

attribute [local instance 10000] CommRing.toCommSemiring CommRing.toRing

noncomputable section

/-! ### `√79` inside `O` -/

/-- `√79`, the second vector of the integral basis. -/
def sd : O := B.equivFun.symm ![0, 1]

lemma sd_sq : sd ^ 2 = 79 := by
  have h : aeval (timesTableO.basis.equivFun.symm ![0, 1]) (ofList [(-79 : ℤ), 0, 1]) = 0 := by
    rw [← minpoly_hroot]; exact minpoly.aeval ℤ _
  rw [T_ofList, T_def] at h
  simp only [map_sub, map_pow, aeval_X, map_ofNat] at h
  exact eq_of_sub_eq_zero h

lemma sd_sq' : sd ^ 2 = ((79 : ℤ) : O) := by push_cast; exact sd_sq

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

/-! ### Expansions in the basis `1, √79` -/

lemma cube_expand (a b : ℤ) :
    ((a : O) + (b : O) * sd) ^ 3
      = ((a ^ 3 + 237 * a * b ^ 2 : ℤ) : O) + ((3 * a ^ 2 * b + 79 * b ^ 3 : ℤ) : O) * sd := by
  push_cast
  linear_combination ((b : O) ^ 3 * sd + 3 * (a : O) * (b : O) ^ 2) * sd_sq

/-- `zeta1 = 80 + 9√79` is the fundamental unit. -/
lemma zeta1_coords : zeta1 = ((80 : ℤ) : O) + ((9 : ℤ) : O) * sd := by
  show B.equivFun.symm ![80, 9] = _
  rw [coord_eq]

lemma mul_zeta1_expand (P Q : ℤ) :
    zeta1 * (((P : ℤ) : O) + ((Q : ℤ) : O) * sd)
      = ((80 * P + 711 * Q : ℤ) : O) + ((9 * P + 80 * Q : ℤ) : O) * sd := by
  rw [zeta1_coords]
  push_cast
  linear_combination (9 * (Q : O)) * sd_sq

/-- `alpha0 = -17 + 2√79`, the generator of `J0 ^ 3`, of norm `-27`. -/
lemma alpha0_coords : alpha0 = ((-17 : ℤ) : O) + ((2 : ℤ) : O) * sd := by
  show B.equivFun.symm ![-17, 2] = _
  rw [coord_eq]

lemma alpha0_mul (y : ℤ) : alpha0 * ((y : O) + sd)
    = (((-17 * y + 158 : ℤ)) : O) + (((2 * y - 17 : ℤ)) : O) * sd := by
  rw [alpha0_coords]; push_cast; linear_combination (2 : O) * sd_sq

lemma alpha0_sq_mul (y : ℤ) : alpha0 ^ 2 * ((y : O) + sd)
    = (((605 * y - 5372 : ℤ)) : O) + (((-68 * y + 605 : ℤ)) : O) * sd := by
  rw [alpha0_coords]; push_cast
  linear_combination (4 * (y : O) + 4 * sd - 68) * sd_sq

/-! ### Arithmetic input -/

lemma hsqfree : Squarefree (79 : ℤ) := Int.squarefree_natCast.mpr (by decide +kernel)

/-- Rewrite `(y : O) + sd` in the shape `coords_inj` consumes. -/
lemma y_add_sd (y : ℤ) : ((y : O) + sd) = (((y : ℤ)) : O) + (((1 : ℤ)) : O) * sd := by
  push_cast; ring

/-! ### The descent -/

/-- `j = 0`: the multiplier is trivial, so the right-hand side is `1` from the start.  `e = 0`
is degenerate; `e = 1` and `e = 2` give the Thue equation, through unimodular substitutions
that also match the two formulas for `x`. -/
lemma branch_zero {x y a b : ℤ} (h : y ^ 2 = x ^ 3 + 79)
    (e : Fin 3) (hmain : ((y : O) + sd)
      = zeta1 ^ (e : ℕ) * (((a : ℤ) : O) + ((b : ℤ) : O) * sd) ^ 3) :
    ∃ A B : ℤ, A ^ 3 + 21 * A ^ 2 * B + 12 * A * B ^ 2 + 2 * B ^ 3 = 1 ∧
      x = 45 * A ^ 2 + 26 * A * B + 2 * B ^ 2 := by
  fin_cases e <;> norm_num at hmain
  · -- `j = 0`, `e = 0` : degenerate, `b ∣ 1` and then `3a² + 79b² = ±1`
    exfalso
    rw [y_add_sd, cube_expand] at hmain
    obtain ⟨-, hF⟩ := coords_inj hmain
    have hbd : (b : ℤ) ∣ 1 := ⟨3 * a ^ 2 + 79 * b ^ 2, by linear_combination hF⟩
    rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hbd) with hb | hb <;> subst hb <;>
      nlinarith [sq_nonneg a, hF]
  · -- `j = 0`, `e = 1` : the Thue equation, via `(A,B) = (-a - 9b, 2a + 19b)`
    rw [y_add_sd, cube_expand, mul_zeta1_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj hmain
    have hT : (9 * a ^ 3 + 240 * a ^ 2 * b + 2133 * a * b ^ 2 + 6320 * b ^ 3 : ℤ) = 1 := by
      linear_combination -hF
    have hx3 : x ^ 3 = (a ^ 2 - 79 * b ^ 2) ^ 3 := by
      linear_combination (-1) * h
        + (80 * a ^ 3 + 2133 * a ^ 2 * b + 18960 * a * b ^ 2 + 56169 * b ^ 3 + y) * hG
        - 79 * (9 * a ^ 3 + 240 * a ^ 2 * b + 2133 * a * b ^ 2 + 6320 * b ^ 3 + 1) * hF
    exact ⟨-a - 9 * b, 2 * a + 19 * b, by linear_combination hT, by
      have := cube_inj hx3; linear_combination this⟩
  · -- `j = 0`, `e = 2` : the same equation, via `(A,B) = (-a - 9b, 11a + 98b)`
    rw [y_add_sd, cube_expand, sq, mul_assoc, mul_zeta1_expand, mul_zeta1_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj hmain
    have hT : (1440 * a ^ 3 + 38397 * a ^ 2 * b + 341280 * a * b ^ 2
        + 1011121 * b ^ 3 : ℤ) = 1 := by linear_combination -hF
    have hx3 : x ^ 3 = (a ^ 2 - 79 * b ^ 2) ^ 3 := by
      linear_combination (-1) * h
        + (12799 * a ^ 3 + 341280 * a ^ 2 * b + 3033363 * a * b ^ 2 + 8987040 * b ^ 3 + y) * hG
        - 79 * (1440 * a ^ 3 + 38397 * a ^ 2 * b + 341280 * a * b ^ 2
            + 1011121 * b ^ 3 + 1) * hF
    exact ⟨-a - 9 * b, 11 * a + 98 * b, by linear_combination hT, by
      have := cube_inj hx3; linear_combination this⟩

/-- `j = 1`: multiplier `alpha0`, right-hand side `-27`.  The equation forces `a ≡ 2b [ZMOD 3]`,
and `a = 2b + 3c` divides it by `27`; all three `e` are then insoluble mod `9`. -/
lemma branch_one {x y a b : ℤ} (h : y ^ 2 = x ^ 3 + 79)
    (e : Fin 3) (hmain : alpha0 * ((y : O) + sd)
      = zeta1 ^ (e : ℕ) * (((a : ℤ) : O) + ((b : ℤ) : O) * sd) ^ 3) :
    False := by
  fin_cases e <;> norm_num at hmain
  · -- `e = 0`
    rw [alpha0_mul, cube_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj hmain
    have hT : (-2 * a ^ 3 - 51 * a ^ 2 * b - 474 * a * b ^ 2 - 1343 * b ^ 3 : ℤ) = -27 := by
      linear_combination 2 * hG + 17 * hF
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
    have hT2 : (-2 * c ^ 3 - 21 * c ^ 2 * b - 78 * c * b ^ 2 - 93 * b ^ 3 : ℤ) = -1 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT)
    have hz := congrArg (fun z : ℤ => (z : ZMod 9)) hT2
    push_cast at hz
    revert hz
    generalize ((c : ZMod 9)) = C9
    generalize ((b : ZMod 9)) = B9
    revert C9 B9
    decide
  · -- `e = 1`
    rw [alpha0_mul, cube_expand, mul_zeta1_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj hmain
    have hT : (-313 * a ^ 3 - 8346 * a ^ 2 * b - 74181 * a * b ^ 2
        - 219778 * b ^ 3 : ℤ) = -27 := by linear_combination 2 * hG + 17 * hF
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
    have hT2 : (-313 * c ^ 3 - 3408 * c ^ 2 * b - 12369 * c * b ^ 2
        - 14964 * b ^ 3 : ℤ) = -1 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT)
    have hz := congrArg (fun z : ℤ => (z : ZMod 9)) hT2
    push_cast at hz
    revert hz
    generalize ((c : ZMod 9)) = C9
    generalize ((b : ZMod 9)) = B9
    revert C9 B9
    decide
  · -- `e = 2`
    rw [alpha0_mul, cube_expand, sq, mul_assoc, mul_zeta1_expand, mul_zeta1_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj hmain
    have hT : (-50078 * a ^ 3 - 1335309 * a ^ 2 * b - 11868486 * a * b ^ 2
        - 35163137 * b ^ 3 : ℤ) = -27 := by linear_combination 2 * hG + 17 * hF
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
    have hT2 : (-50078 * c ^ 3 - 545259 * c ^ 2 * b - 1978962 * c * b ^ 2
        - 2394147 * b ^ 3 : ℤ) = -1 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT)
    have hz := congrArg (fun z : ℤ => (z : ZMod 9)) hT2
    push_cast at hz
    revert hz
    generalize ((c : ZMod 9)) = C9
    generalize ((b : ZMod 9)) = B9
    revert C9 B9
    decide

/-- `j = 2`: multiplier `alpha0 ^ 2`, right-hand side `729`; two substitutions, each dividing by
`27` (`a = 2b + 3c`, then `c = b + 3f`).  All three `e` are insoluble mod `9`. -/
lemma branch_two {x y a b : ℤ} (h : y ^ 2 = x ^ 3 + 79)
    (e : Fin 3) (hmain : alpha0 ^ 2 * ((y : O) + sd)
      = zeta1 ^ (e : ℕ) * (((a : ℤ) : O) + ((b : ℤ) : O) * sd) ^ 3) :
    False := by
  fin_cases e <;> norm_num at hmain
  · -- `e = 0`
    rw [alpha0_sq_mul, cube_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj hmain
    have hT : (68 * a ^ 3 + 1815 * a ^ 2 * b + 16116 * a * b ^ 2
        + 47795 * b ^ 3 : ℤ) = 729 := by linear_combination -68 * hG - 605 * hF
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
    have hT2 : (68 * c ^ 3 + 741 * c ^ 2 * b + 2688 * c * b ^ 2 + 3253 * b ^ 3 : ℤ) = 27 :=
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
    have hT3 : (68 * f ^ 3 + 315 * f ^ 2 * b + 486 * f * b ^ 2 + 250 * b ^ 3 : ℤ) = 1 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT2)
    have hz := congrArg (fun z : ℤ => (z : ZMod 9)) hT3
    push_cast at hz
    revert hz
    generalize ((f : ZMod 9)) = F9
    generalize ((b : ZMod 9)) = B9
    revert F9 B9
    decide
  · -- `e = 1`
    rw [alpha0_sq_mul, cube_expand, mul_zeta1_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj hmain
    have hT : (10885 * a ^ 3 + 290244 * a ^ 2 * b + 2579745 * a * b ^ 2
        + 7643092 * b ^ 3 : ℤ) = 729 := by linear_combination -68 * hG - 605 * hF
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
    have hT2 : (10885 * c ^ 3 + 118518 * c ^ 2 * b + 430149 * c * b ^ 2
        + 520394 * b ^ 3 : ℤ) = 27 :=
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
    have hT3 : (10885 * f ^ 3 + 50391 * f ^ 2 * b + 77760 * f * b ^ 2
        + 39998 * b ^ 3 : ℤ) = 1 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT2)
    have hz := congrArg (fun z : ℤ => (z : ZMod 9)) hT3
    push_cast at hz
    revert hz
    generalize ((f : ZMod 9)) = F9
    generalize ((b : ZMod 9)) = B9
    revert F9 B9
    decide
  · -- `e = 2`
    rw [alpha0_sq_mul, cube_expand, sq, mul_assoc, mul_zeta1_expand, mul_zeta1_expand] at hmain
    obtain ⟨hG, hF⟩ := coords_inj hmain
    have hT : (1741532 * a ^ 3 + 46437225 * a ^ 2 * b + 412743084 * a * b ^ 2
        + 1222846925 * b ^ 3 : ℤ) = 729 := by linear_combination -68 * hG - 605 * hF
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
    have hT2 : (1741532 * c ^ 3 + 18962139 * c ^ 2 * b + 68821152 * c * b ^ 2
        + 83259787 * b ^ 3 : ℤ) = 27 :=
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
    have hT3 : (1741532 * f ^ 3 + 8062245 * f ^ 2 * b + 12441114 * f * b ^ 2
        + 6399430 * b ^ 3 : ℤ) = 1 :=
      mul_left_cancel₀ (by norm_num : (27 : ℤ) ≠ 0) (by linear_combination hT2)
    have hz := congrArg (fun z : ℤ => (z : ZMod 9)) hT3
    push_cast at hz
    revert hz
    generalize ((f : ZMod 9)) = F9
    generalize ((b : ZMod 9)) = B9
    revert F9 B9
    decide

/-- **Mordell implies Thue for `d = 79`.**

The nine `(j, e)` branches collapse to a single Thue equation: `(0,0)` is degenerate, the six
with `j ≠ 0` are insoluble mod `9`, and the two survivors `(0,1)`, `(0,2)` give forms that are
`GL₂(ℤ)`-equivalent, with the same formula for `x`.  The cubic is the norm form of `θ` with
`θ³ + 21θ² + 12θ + 2 = 0`, a generator of the field of discriminant `-948` and class number
`1`; its form discriminant is `-8532 = -108 · 79`. -/
theorem mordell79_imp_thue {x y : ℤ} (h : y ^ 2 = x ^ 3 + 79) :
    ∃ A B : ℤ, A ^ 3 + 21 * A ^ 2 * B + 12 * A * B ^ 2 + 2 * B ^ 3 = 1 ∧
      x = 45 * A ^ 2 + 26 * A * B + 2 * B ^ 2 := by
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
  · exact branch_zero h e hmain
  · exact absurd hmain (fun hc => branch_one h e hc)
  · exact absurd hmain (fun hc => branch_two h e hc)

end
