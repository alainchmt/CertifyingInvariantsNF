import IdealArithmetic.MordellExamples.MordellExample17.NF2_2_17_1.Invariants2_2_17_1

namespace NF2_2_17_1

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^2 - 17`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^2 - 17)) := rfl

lemma T_irreducible' : Irreducible (X^2 - 17 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = 17 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 0 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 2 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 1 , (ZMod (![1] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_1' : classNumber K = 1 := class_number_K_eq_1

end

end NF2_2_17_1
