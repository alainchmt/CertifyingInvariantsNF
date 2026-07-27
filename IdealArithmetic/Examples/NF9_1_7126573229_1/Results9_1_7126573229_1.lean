import IdealArithmetic.Examples.NF9_1_7126573229_1.Invariants9_1_7126573229_1

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^9 - X^8 + 5*X^7 - 6*X^6 + 5*X^5 - 14*X^4 - 3*X^3 - 10*X^2 - 3*X - 1`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^9 - X^8 + 5*X^7 - 6*X^6 + 5*X^5 - 14*X^4 - 3*X^3 - 10*X^2 - 3*X - 1)) := rfl

lemma T_irreducible' : Irreducible (X^9 - X^8 + 5*X^7 - 6*X^6 + 5*X^5 - 14*X^4 - 3*X^3 - 10*X^2 - 3*X - 1 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = 7126573229 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 4 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 1 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 1 , (ZMod (![2] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_2' : classNumber K = 2 := class_number_K_eq_2
