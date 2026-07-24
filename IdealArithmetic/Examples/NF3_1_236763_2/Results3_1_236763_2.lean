import IdealArithmetic.Examples.NF3_1_236763_2.Invariants3_1_236763_2

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^3 + 141*X - 382`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^3 + 141*X - 382)) := rfl

lemma T_irreducible' : Irreducible (X^3 + 141*X - 382 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = -236763 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 1 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 1 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 1 , (ZMod (![3] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_3' : classNumber K = 3 := class_number_K_eq_3
