import IdealArithmetic.MordellExamples.MordellExample142.ThueReduction142
import IdealArithmetic.MordellExamples.MordellExample142.SolutionThue1704

/-!
# `y ^ 2 = x ^ 3 + 142` has exactly the two integral points

Assembly of the two halves of the argument:

* `mordell142_imp_thue` (`ThueReduction142`): class-group descent in `ℚ(√142)`, whose class
  number is `3`, turning a Mordell solution into a solution of a single Thue equation
  together with the formula recovering `x`;
* `thue_eq_one_iff_3_1_1704_1` (`SolutionThue1704`), the complete solution set of that Thue
  equation by the elementary Skolem method:

  | Thue equation | cubic field | `p`, `f` | solutions | `x` |
  |---|---|---|---|---|
  | `A³ + 15A²B + 66AB² + 106B³ = 1` | `X³+15X²+66X+106` | `13`, `12` | `(1,0)` | `3` |

Once `x` is known, `y` is determined up to sign by the equation itself, which is why the
descent only ever had to conclude about `x`.

Opus 5
-/

set_option linter.all false

open Mordell

/-- **The `x`-coordinate of the integral points of `y² = x³ + 142`.** -/
theorem mordell142_x {x y : ℤ} (h : y ^ 2 = x ^ 3 + 142) : x = 3 := by
  obtain ⟨A, B, ht, hx⟩ := mordell142_imp_thue h
  obtain ⟨rfl, rfl⟩ := (NF3_1_1704_1.thue_eq_one_iff_3_1_1704_1 A B).mp ht
  omega

/-- **The integral points of the Mordell curve `y² = x³ + 142`.** -/
theorem mordell_142_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 + 142 ↔ (x = 3 ∧ y = 13) ∨ (x = 3 ∧ y = -13) := by
  constructor
  · intro h
    obtain rfl := mordell142_x h
    rcases mul_eq_zero.mp (show (y - 13) * (y + 13) = 0 by grind) with h' | h'
    exacts [Or.inl ⟨rfl, by omega⟩, Or.inr ⟨rfl, by omega⟩]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
