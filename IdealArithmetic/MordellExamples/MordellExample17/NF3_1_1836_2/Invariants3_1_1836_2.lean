import IdealArithmetic.MordellExamples.MordellExample17.NF3_1_1836_2.UnitsData3_1_1836_2
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Signature.ResultantRecursive
import IdealArithmetic.DedekindProject.Discriminant

namespace NF3_1_1836_2

set_option linter.all false

/- Number field `K(α)` with α root of polynomial `X^3 + 6*X - 6`. -/

/- Ring of integers with basis `[1, t, t^2]` -/

open BigOperators Classical Matrix Polynomial Module

noncomputable section

instance hirr : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

instance K_field : Field K := by
  unfold K
  exact AdjoinRoot.instField

instance K_numberField : NumberField K := by
  unfold K
  exact AdjoinRoot.instNumberFieldRat

instance : Module ℚ K := Algebra.toModule
instance : @Algebra ℤ K CommRing.toCommSemiring CommRing.toCommSemiring.toSemiring := Ring.toIntAlgebra K
instance : @CharZero K CommRing.toCommSemiring.toNonAssocSemiring.toAddCommMonoidWithOne.toAddMonoidWithOne := charZero_of_expChar_one' K

lemma K_finrank : Module.finrank ℚ K = 3 := by
  unfold K
  erw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux _), Polynomial.natDegree_map_eq_of_injective, T_degree]
  · simp
  · exact RingHom.injective_int (algebraMap ℤ ℚ)
  · exact Irreducible.ne_zero hirr.out

theorem O_integral_closure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ []
  · fin_cases hc
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T _ T_ofList [] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_integral_closure] ; rfl

instance : Module.Finite ℤ (Additive ((↥O)ˣ ⧸ CommGroup.torsion (↥O)ˣ)) := by
  rw [O_integral_closure]
  exact NumberField.Units.instFiniteIntAdditiveQuotientUnitsRingOfIntegersSubgroupTorsion K

instance : Module.Free ℤ (Additive ((↥O)ˣ ⧸ CommGroup.torsion (↥O)ˣ)) := by
  rw [O_integral_closure]
  exact NumberField.Units.instFreeIntAdditiveQuotientUnitsRingOfIntegersSubgroupTorsion K

instance :  Fintype ↥(CommGroup.torsion (↥O)ˣ) := by
  rw [O_integral_closure]
  exact NumberField.Units.instFintypeSubtypeUnitsRingOfIntegersMemSubgroupTorsion K

instance : IsCyclic ↥(CommGroup.torsion (↥O)ˣ) := by
  rw [O_integral_closure]
  exact NumberField.Units.instIsCyclicSubtypeUnitsRingOfIntegersMemSubgroupTorsion K

instance DD' : IsDedekindDomain O  := by
  rw [O_integral_closure]
  exact integralClosure.isDedekindDomain ℤ ℚ K

instance : Module.Free ℤ ↥O := Module.Free.of_basis B

instance  : IdemCommSemiring (Ideal O) := Ideal.instIdemCommSemiring
instance : CharZero O := SubsemiringClass.instCharZero O

def SturmRC : SturmBuilderOfList [[-6, 6, 0, 1], [6, 0, 3], [54, -36], [-1836]] [-6, 6, 0, 1] [6, 0, 3] where
  hlen := by decide
  h0 := by decide
  h1 := by decide
  hlast := by decide
  hdrop := by decide
  hmono := by
    dsimp
    intro i hic
    have hi : i < 3 := by omega
    interval_cases i <;> (dsimp ; decide)
  e := [9, 1296]
  f := [1, 9]
  epos := by decide
  fpos := by decide
  Q := [[0, 3], [-162, -108]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    dsimp
    intro i hi
    have hi : i < 2 := by omega
    interval_cases i <;> (dsimp ; decide)

def RC : RankUnitsCertificate O where
  f := X^3 + 6*X - 6
  l := [-6, 6, 0, 1]
  hl := T_ofList
  hlz := by decide
  hz := by decide
  hAdj := Adj
  heq := O_integral_closure
  P := [[-6, 6, 0, 1], [6, 0, 3], [54, -36], [-1836]]
  SB := SturmRC
  k := 1
  r := 2
  hr := by decide
  hreq := by decide 


lemma T_discr : T.discr = -1836 :=  by
  convert discriminant_eq_DiscriminantOfPRemainder_of_SturmBuilderOfList SturmRC
  rw [T_ofList]

theorem K_discr : NumberField.discr K = -1836 := by
  rw [discr_numberField_eq_discrSubalgebraBuilder T_irreducible BQ O_integral_closure]
  rw [T_discr]
  rfl

lemma K_nrComplexPlaces : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
  rw [nrComplexPlaces_of_RankUnitsCertificate RC]
  rfl

lemma K_nrRealPlaces : NumberField.InfinitePlace.nrRealPlaces K = 1 := by
  rw [nrRealPlaces_of_RankUnitsCertificate RC]
  rfl

end

end NF3_1_1836_2
