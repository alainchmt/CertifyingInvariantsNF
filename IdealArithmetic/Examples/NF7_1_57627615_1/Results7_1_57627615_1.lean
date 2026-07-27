import IdealArithmetic.Examples.NF7_1_57627615_1.Invariants7_1_57627615_1

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^7 - X^6 - 5*X^4 - 5*X^2 + 2*X - 1`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^7 - X^6 - 5*X^4 - 5*X^2 + 2*X - 1)) := rfl

lemma T_irreducible' : Irreducible (X^7 - X^6 - 5*X^4 - 5*X^2 + 2*X - 1 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = -57627615 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 3 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 1 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 1 , (ZMod (![3] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_3' : classNumber K = 3 := class_number_K_eq_3
