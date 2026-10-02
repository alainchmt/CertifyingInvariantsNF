import IdealArithmetic.MordellExamples.MordellExample2026.NF2_2_8104_1.Invariants2_2_8104_1

namespace NF2_2_8104_1

noncomputable section

open Polynomial NumberField

/- Number field `K(α)` with `α` root of the polynomial `X^2 - 2026`. -/

lemma T_def' : K = AdjoinRoot (map (algebraMap ℤ ℚ) (X^2 - 2026)) := rfl

lemma T_irreducible' : Irreducible (X^2 - 2026 : ℤ[X]) := irreducible_T

theorem O_ringOfIntegers : O = RingOfIntegers K := O_ringOfIntegers'

theorem K_discr' : discr K = 8104 := K_discr

lemma K_nrComplexPlaces' : InfinitePlace.nrComplexPlaces K = 0 := K_nrComplexPlaces

lemma K_nrRealPlaces' : InfinitePlace.nrRealPlaces K = 2 := K_nrRealPlaces

def class_group_equiv' :
  (∀ i : Fin 1 , (ZMod (![14] i))) ≃+ Additive (ClassGroup (RingOfIntegers K)) := class_group_equiv

theorem class_number_K_eq_14' : classNumber K = 14 := class_number_K_eq_14

end

end NF2_2_8104_1
