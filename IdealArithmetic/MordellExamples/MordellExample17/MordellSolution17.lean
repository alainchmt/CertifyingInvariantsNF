import IdealArithmetic.MordellExamples.MordellExample17.ThueReduction17
import IdealArithmetic.MordellExamples.MordellExample17.SolutionThue459
import IdealArithmetic.MordellExamples.MordellExample17.SolutionThue1836a
import IdealArithmetic.MordellExamples.MordellExample17.SolutionThue1836b
import IdealArithmetic.MordellExamples.MordellExample17.SolutionThue204

/-!
# `y ^ 2 = x ^ 3 + 17` has exactly the sixteen integral points

Assembly of the two halves of the argument:

* `mordell17_imp_thue` (`ThueReduction17`): class-group descent in `ℚ(√17)`, whose class
  number is `1`, turning a Mordell solution into a solution of one of four Thue equations
  together with the formula recovering `x`;
* the four solution files, each giving the complete solution set of its Thue equation by the
  elementary Skolem method:

  | Thue equation | cubic field | `p`, `f` | solutions | `x` |
  |---|---|---|---|---|
  | `A³ + 3AB² - 8B³ = 1`   | `X³+3X-8`   | `11`, `10`  | `(1,0), (-3,-2)`         | `-1, 43` |
  | `A³ - 6AB² - 10B³ = 1`  | `X³-6X-10`  | `349`, `116`| `(1,0), (-3,-1)`         | `2, 52` |
  | `A³ + 6AB² - 6B³ = 1`   | `X³+6X-6`   | `409`, `136`| `(1,0), (1,1), (-23,-26)`| `-2, 8, 5234` |
  | `A³ - 12AB² - 18B³ = 1` | `X³-12X-18` | `307`, `102`| `(1,0)`                  | `4` |

Once `x` is known, `y` is determined up to sign by the equation itself, which is why the
descent only ever had to conclude about `x`.

Opus 5
-/

set_option linter.all false

open Mordell

/-- With `x` fixed, the equation determines `y` up to sign. -/
lemma eq_or_eq_neg_of_sq_eq {y d : ℤ} (h : y ^ 2 = d ^ 2) : y = d ∨ y = -d := by
  rcases mul_eq_zero.mp (show (y - d) * (y + d) = 0 by grind) with h' | h'
  exacts [Or.inl (by omega), Or.inr (by omega)]

/-- **The `x`-coordinates of the integral points of `y² = x³ + 17`.** -/
theorem mordell17_x {x y : ℤ} (h : y ^ 2 = x ^ 3 + 17) :
    x = -2 ∨ x = -1 ∨ x = 2 ∨ x = 4 ∨ x = 8 ∨ x = 43 ∨ x = 52 ∨ x = 5234 := by
  obtain ⟨A, B, hc⟩ := mordell17_imp_thue h
  rcases hc with ⟨ht, hx⟩ | ⟨ht, hx⟩ | ⟨ht, hx⟩ | ⟨ht, hx⟩
  · rcases (NF3_1_459_1.thue_eq_one_iff_3_1_459_1 A B).mp ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num at hx <;> omega
  · rcases (NF3_1_1836_1.thue_eq_one_iff_3_1_1836_1 A B).mp ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      norm_num at hx <;> omega
  · rcases (NF3_1_1836_2.thue_eq_one_iff_3_1_1836_2 A B).mp ht with
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num at hx <;> omega
  · rcases (NF3_1_204_1.thue_eq_one_iff_3_1_204_1 A B).mp ht with ⟨rfl, rfl⟩ <;>
      norm_num at hx <;> omega

/-- **The integral points of the Mordell curve `y² = x³ + 17`.** -/
theorem mordell_17_iff (x y : ℤ) :
    y ^ 2 = x ^ 3 + 17 ↔
      (x = -2 ∧ y = 3) ∨ (x = -2 ∧ y = -3) ∨
      (x = -1 ∧ y = 4) ∨ (x = -1 ∧ y = -4) ∨
      (x = 2 ∧ y = 5) ∨ (x = 2 ∧ y = -5) ∨
      (x = 4 ∧ y = 9) ∨ (x = 4 ∧ y = -9) ∨
      (x = 8 ∧ y = 23) ∨ (x = 8 ∧ y = -23) ∨
      (x = 43 ∧ y = 282) ∨ (x = 43 ∧ y = -282) ∨
      (x = 52 ∧ y = 375) ∨ (x = 52 ∧ y = -375) ∨
      (x = 5234 ∧ y = 378661) ∨ (x = 5234 ∧ y = -378661) := by
  constructor
  · intro h
    rcases mordell17_x h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rcases eq_or_eq_neg_of_sq_eq (y := y) (d := 3) (by grind) with rfl | rfl <;> norm_num
    · rcases eq_or_eq_neg_of_sq_eq (y := y) (d := 4) (by grind) with rfl | rfl <;> norm_num
    · rcases eq_or_eq_neg_of_sq_eq (y := y) (d := 5) (by grind) with rfl | rfl <;> norm_num
    · rcases eq_or_eq_neg_of_sq_eq (y := y) (d := 9) (by grind) with rfl | rfl <;> norm_num
    · rcases eq_or_eq_neg_of_sq_eq (y := y) (d := 23) (by grind) with rfl | rfl <;> norm_num
    · rcases eq_or_eq_neg_of_sq_eq (y := y) (d := 282) (by grind) with rfl | rfl <;> norm_num
    · rcases eq_or_eq_neg_of_sq_eq (y := y) (d := 375) (by grind) with rfl | rfl <;> norm_num
    · rcases eq_or_eq_neg_of_sq_eq (y := y) (d := 378661) (by grind) with rfl | rfl <;> norm_num
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> norm_num
