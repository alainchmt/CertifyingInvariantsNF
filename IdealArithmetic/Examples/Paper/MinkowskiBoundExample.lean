import IdealArithmetic.Examples.Paper.NF4_4_54381317_1.Invariants

/- The number field `K` has defining polynomial `X^4 - X^3 - 80*X^2 - 332*X - 383`.  -/


/- After certifying its discriminant and signature, we prove a numerical bound for its
Minkowski bound.  -/
theorem K_minowski : minkowskiBoundFB K ≤ 691.357086451742 := by
  refine K_minkowski_decimal _ ?_
  erw [K_nrComplexPlaces, K_discr, K_finrank]
  have hraux: √54381317 ≤ 7374.368931999999 := by
      refine Real.sqrt_le_iff.mpr ?_
      norm_num
  have : 0.09375 * √54381317 ≤ 691.357087 := by
    refine le_trans (mul_le_mul_of_nonneg (by rfl) hraux (by norm_num) (by norm_num)) ?_
    norm_num
  norm_num
  try {linarith}
