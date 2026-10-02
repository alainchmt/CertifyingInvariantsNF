import IdealArithmetic.MordellExamples.MordellExample79.ThueReduction79
import IdealArithmetic.MordellExamples.MordellExample79.SolutionThue948

/-!
# `y ^ 2 = x ^ 3 + 79` has exactly the two integral points

Assembly of the two halves of the argument:

* `mordell79_imp_thue` (`ThueReduction79`): class-group descent in `ℚ(√79)`, whose class
  number is `3` -- the smallest `d` for which `3 ∣ h` -- turning a Mordell solution into a
  solution of a single Thue equation together with the formula recovering `x`;
* `thue_eq_one_iff_3_1_948_1` (`SolutionThue948`), the complete solution set of that Thue
  equation by the elementary Skolem method:

  | Thue equation | cubic field | `p`, `f` | solutions | `x` |
  |---|---|---|---|---|
  | `A³ + 21A²B + 12AB² + 2B³ = 1` | `X³+21X²+12X+2` | `53`, `26` | `(1,0)` | `45` |

Once `x` is known, `y` is determined up to sign by the equation itself, which is why the
descent only ever had to conclude about `x`.

Opus 5
-/

set_option linter.all false

open Mordell

/-- **The `x`-coordinate of the integral points of `y² = x³ + 79`.** -/
theorem mordell79_x {x y : ℤ} (h : y ^ 2 = x ^ 3 + 79) : x = 45 := by
  obtain ⟨A, B, ht, hx⟩ := mordell79_imp_thue h
  obtain ⟨rfl, rfl⟩ := (NF3_1_948_1.thue_eq_one_iff_3_1_948_1 A B).mp ht
  omega

/-- **The integral points of the Mordell curve `y² = x³ + 79`.** -/
theorem mordell_79_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 + 79 ↔ (x = 45 ∧ y = 302) ∨ (x = 45 ∧ y = -302) := by
  constructor
  · intro h
    obtain rfl := mordell79_x h
    rcases mul_eq_zero.mp (show (y - 302) * (y + 302) = 0 by grind) with h' | h'
    exacts [Or.inl ⟨rfl, by omega⟩, Or.inr ⟨rfl, by omega⟩]
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
