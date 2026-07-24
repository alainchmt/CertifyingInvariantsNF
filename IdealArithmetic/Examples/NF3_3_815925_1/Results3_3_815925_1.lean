import IdealArithmetic.Examples.NF3_3_815925_1.Invariants3_3_815925_1

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^3 - X^2 - 148*X + 52`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^3 - X^2 - 148*X + 52)) := rfl

lemma T_irreducible' : Irreducible (X^3 - X^2 - 148*X + 52 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = 815925 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 0 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 3 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 1 , (ZMod (![2] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_2' : classNumber K = 2 := class_number_K_eq_2
