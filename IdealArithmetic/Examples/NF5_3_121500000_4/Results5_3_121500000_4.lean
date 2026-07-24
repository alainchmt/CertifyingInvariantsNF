import IdealArithmetic.Examples.NF5_3_121500000_4.Invariants5_3_121500000_4

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^5 - 30*X^3 - 10*X^2 + 225*X + 270`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^5 - 30*X^3 - 10*X^2 + 225*X + 270)) := rfl

lemma T_irreducible' : Irreducible (X^5 - 30*X^3 - 10*X^2 + 225*X + 270 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = -121500000 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 1 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 3 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 1 , (ZMod (![1] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_1' : classNumber K = 1 := class_number_K_eq_1
