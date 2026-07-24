import IdealArithmetic.Examples.NF3_3_895700_1.Invariants3_3_895700_1

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^3 - X^2 - 173*X + 857`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^3 - X^2 - 173*X + 857)) := rfl

lemma T_irreducible' : Irreducible (X^3 - X^2 - 173*X + 857 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = 895700 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 0 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 3 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 2 , (ZMod (![3, 3] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_9' : classNumber K = 9 := class_number_K_eq_9
