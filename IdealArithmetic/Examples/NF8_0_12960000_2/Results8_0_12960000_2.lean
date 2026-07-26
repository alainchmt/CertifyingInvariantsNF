import IdealArithmetic.Examples.NF8_0_12960000_2.Invariants8_0_12960000_2

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^8 - X^6 + 2*X^4 + X^2 + 1`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^8 - X^6 + 2*X^4 + X^2 + 1)) := rfl

lemma T_irreducible' : Irreducible (X^8 - X^6 + 2*X^4 + X^2 + 1 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = 12960000 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 4 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 0 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 1 , (ZMod (![1] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_1' : classNumber K = 1 := class_number_K_eq_1
