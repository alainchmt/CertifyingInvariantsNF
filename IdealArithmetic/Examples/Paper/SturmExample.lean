import IdealArithmetic.Signature.ResultantRecursive


open Polynomial

noncomputable section

local notation "T" => (X ^5 - 3 * X ^3 + 9 * X - 8 : ℤ[X])

/- We construct a Sturm sequence -/
def S : SturmBuilderOfList [[-8, 9, 0, -3, 0, 1], [9, 0, -9, 0, 5], [20, -18, 0, 3],
    [-27, 100, -63], [-4752, 3103], [1]] [-8, 9, 0, -3, 0, 1] [9, 0, -9, 0, 5] where
  hlen := by decide
  h0 := by decide
  h1 := by decide
  hlast := by decide
  hdrop := by decide
  hmono := by
    dsimp
    intro i hic
    have hi : i < 5 := by omega
    interval_cases i <;> (dsimp ; decide)
  e := [25, 9, 3969, 9628609]
  f := [10, 3, 15, 208061595]
  epos := by decide
  fpos := by decide
  Q := [[0, 5], [0, 15], [-300, -189], [10924, -195489]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    dsimp
    intro i hi
    have hi : i < 4 := by omega
    interval_cases i <;> dsimp <;> decide

open Finset

/-- The polynomial `X ^ 5 - 3 * X ^ 3 + 9 * X - 8` over `ℝ` has exactly `1` root -/
theorem real_roots :
    #(Multiset.toFinset (X ^ 5 - 3 * X ^ 3 + 9 * X - 8 : ℝ[X] ).roots) = 1 := by
  have : (List.derivative [-8, 9, 0, -3, 0, 1]).dropTrailingZeros = [9, 0, -9, 0, 5]:= by decide
  convert sturm_theorem_total_map_ofList ℝ (Real.IsRealClosedField) (algebraMap ℤ ℝ)
    (Int.cast_strictMono) (this ▸ S)
  · simp ; ring

/- The discriminant of the polynomial -/
lemma T_discr : discr T = 2516240 :=  by
  convert discriminant_eq_DiscriminantOfPRemainder_of_SturmBuilderOfList S
  norm_num ; ring
