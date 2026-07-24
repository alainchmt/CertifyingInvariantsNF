import IdealArithmetic.Examples.NF5_3_18225000000_2.Invariants5_3_18225000000_2

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^5 - 90*X^3 - 240*X^2 + 2160*X + 10368`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^5 - 90*X^3 - 240*X^2 + 2160*X + 10368)) := rfl

lemma T_irreducible' : Irreducible (X^5 - 90*X^3 - 240*X^2 + 2160*X + 10368 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = -18225000000 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 1 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 3 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 1 , (ZMod (![5] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_5' : classNumber K = 5 := class_number_K_eq_5
