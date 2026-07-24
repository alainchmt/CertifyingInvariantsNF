import IdealArithmetic.Examples.NF3_1_378695_1.Invariants3_1_378695_1

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^3 - X^2 - 46*X + 185`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^3 - X^2 - 46*X + 185)) := rfl

lemma T_irreducible' : Irreducible (X^3 - X^2 - 46*X + 185 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = -378695 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 1 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 1 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 1 , (ZMod (![2] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_2' : classNumber K = 2 := class_number_K_eq_2
