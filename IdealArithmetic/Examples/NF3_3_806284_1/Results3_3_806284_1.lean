import IdealArithmetic.Examples.NF3_3_806284_1.Invariants3_3_806284_1

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^3 - 103*X - 206`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^3 - 103*X - 206)) := rfl

lemma T_irreducible' : Irreducible (X^3 - 103*X - 206 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = 806284 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 0 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 3 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 1 , (ZMod (![3] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_3' : classNumber K = 3 := class_number_K_eq_3
