import IdealArithmetic.Examples.Paper.NF5_1_157265_1.RI5_1_157265_1
import IdealArithmetic.Examples.Paper.SturmExample
import IdealArithmetic.Saturation.CertifyTorsionOrder

/- The number field `K` wth defining polynomial `X^5 - 3*X^3 + 9*X - 8` and explicit
ring of integers `O`.  -/

open Polynomial

noncomputable section

/- This structure certifies the signature of a number field (and thus the rank of its unit group)
via a Sturm sequence coming from `S`, using Sturm's theorem. -/

def RC : RankUnitsCertificate O where
  f := X^5 - 3*X^3 + 9*X - 8
  l := [-8, 9, 0, -3, 0, 1]
  hl := T_ofList
  hlz := by decide
  hz := by decide
  hAdj := Adj
  heq := O_integral_closure
  P := [[-8, 9, 0, -3, 0, 1], [9, 0, -9, 0, 5], [20, -18, 0, 3],
    [-27, 100, -63], [-4752, 3103], [1]]
  SB := S
  k := 1
  r := 3
  hr := by decide
  hreq := by decide

/- The discriminant of the number field is computed from the discriminant of
the defining polynomial `T_discr` and an integral basis for the ring of integers. -/
theorem K_discr : NumberField.discr K = 157265 := by
  rw [discr_numberField_eq_discrSubalgebraBuilder T_irreducible BQ O_integral_closure]
  erw [T_discr]
  rfl

/- The number `r₂` of pairs of complex embeddings.  -/
lemma K_nrComplexPlaces : NumberField.InfinitePlace.nrComplexPlaces K = 2 := by
  rw [nrComplexPlaces_of_RankUnitsCertificate RC]
  rfl

/- The number `r₁` of pairs of real embeddings.  -/
lemma K_nrRealPlaces : NumberField.InfinitePlace.nrRealPlaces K = 1 := by
  rw [nrRealPlaces_of_RankUnitsCertificate RC]
  rfl

/- The rank of the unit group  -/
lemma K_units  : Module.finrank ℤ (Additive (Oˣ ⧸ (CommGroup.torsion Oˣ))) = 2  := by
  refine units_finrank_of_RankUnitsCertificate RC
