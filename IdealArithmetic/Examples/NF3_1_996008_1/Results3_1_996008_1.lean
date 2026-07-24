import IdealArithmetic.Examples.NF3_1_996008_1.Invariants3_1_996008_1

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^3 - 25*X - 198`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^3 - 25*X - 198)) := rfl

lemma T_irreducible' : Irreducible (X^3 - 25*X - 198 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = -996008 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 1 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 1 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 2 , (ZMod (![8, 2] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_16' : classNumber K = 16 := class_number_K_eq_16
