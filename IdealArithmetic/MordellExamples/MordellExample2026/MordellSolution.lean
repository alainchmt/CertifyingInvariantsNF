import IdealArithmetic.MordellExamples.MordellExample2026.ThueReduction
import IdealArithmetic.MordellExamples.MordellExample2026.SolutionThue1

/-!
# `y ^ 2 = x ^ 3 + 2026` has exactly the solutions `(-1, ±45)`

Assembly of the two halves of the argument:

* `mordell_imp_thue` (`ThueReduction`): class-group descent in `ℚ(√2026)`, whose class number
  `14` is prime to `3`, turning a Mordell solution into a solution of the Thue equation
  `A ^ 3 + 3AB ^ 2 - 90B ^ 3 = 1` together with the formula recovering `x`;
* `thue_eq_one_iff_3_1_24312_1` (`SolutionThue1`): that Thue equation has only `(A, B) = (1, 0)`,
  by the elementary Skolem method at `p = 83`.

Once `x` is known, `y` is determined up to sign by the equation itself, which is why the
descent only ever had to conclude about `x`.

Opus 5
-/

open Mordell

/-- **The `x`-coordinate of the integral points of `y² = x³ + 2026`.** -/
theorem mordell2026_x {x y : ℤ} (h : y ^ 2 = x ^ 3 + 2026) : x = -1 := by
  obtain ⟨A, B, ht, hx⟩ := mordell_imp_thue h
  obtain ⟨rfl, rfl⟩ := (thue_eq_one_iff_3_1_24312_1 A B).mp ht
  omega

/-- **The integral points of the Mordell curve `y² = x³ + 2026`.** -/
theorem mordell_2026_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 + 2026 ↔ (x = -1 ∧ y = 45) ∨ (x = -1 ∧ y = -45) := by
  constructor
  · intro h
    obtain rfl := mordell2026_x h
    rcases mul_eq_zero.mp (show (y - 45) * (y + 45) = 0 by grind) with h' | h'
    exacts [Or.inl ⟨rfl, by omega⟩, Or.inr ⟨rfl, by omega⟩]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
