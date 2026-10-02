import IdealArithmetic.MordellExamples.MordellExample142.NF3_1_1704_1.UnitsSaturated3_1_1704_1_2
import IdealArithmetic.MordellExamples.MordellExample142.NF3_1_1704_1.UnitsSaturated3_1_1704_1_3
import IdealArithmetic.MordellExamples.MordellExample142.NF3_1_1704_1.UnitsSaturated3_1_1704_1_5
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Signature.ResultantRecursive
import IdealArithmetic.DedekindProject.Discriminant

namespace NF3_1_1704_1

set_option linter.all false

/- Number field `K(α)` with α root of polynomial `X^3 + 15*X^2 + 66*X + 106`. -/

/- Ring of integers with basis `[1, t, 1/3*t^2 + 2/3*t + 1/3]` -/

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
  by_cases hc : p ∈ [3]
  · fin_cases hc
    exact @pMaximal_of_MaximalOrderCertificateLists K 3 _ IsAddTorsionFree.to_noZeroSMulDivisors_int _ O Om hm _ _ M3
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T _ T_ofList [3] D p hp hc)
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

def SturmRC : SturmBuilderOfList [[106, 66, 15, 1], [66, 30, 3], [36, 54], [-15336]] [106, 66, 15, 1] [66, 30, 3] where
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
  e := [9, 2916]
  f := [1, 9]
  epos := by decide
  fpos := by decide
  Q := [[15, 3], [1512, 162]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    dsimp
    intro i hi
    have hi : i < 2 := by omega
    interval_cases i <;> (dsimp ; decide)

def RC : RankUnitsCertificate O where
  f := X^3 + 15*X^2 + 66*X + 106
  l := [106, 66, 15, 1]
  hl := T_ofList
  hlz := by decide
  hz := by decide
  hAdj := Adj
  heq := O_integral_closure
  P := [[106, 66, 15, 1], [66, 30, 3], [36, 54], [-15336]]
  SB := SturmRC
  k := 1
  r := 2
  hr := by decide
  hreq := by decide 

def NPCU2 : pMaximalUnitsCertificateDvdT O 2 where 
 hp := by decide
 r := 1
 huc := by 
  erw [units_finrank_of_RankUnitsCertificate RC]
  decide
 u := ![zeta1]
 hu := fun i => 
  match i with 
  | 0 => isUnit_zeta1
 v := v
 m := 2
 hm := by norm_num
 hmv := v_pow_one
 t := 2
 hrle := by decide
 q := ![3, 13]
 hqP := by 
  intro i 
  match i with 
  | 0 => exact Sat2.hq3
  | 1 => exact Sat2.hq13
 I := ![Sat2.I0, Sat2.I1]
 hcard := fun i =>
  match i with  
  | 0 => Sat2.N0
  | 1 => Sat2.N1
 ζ := ![2, 2]
 hr := fun i =>
  match i with 
  | 0 => ((orderOf_of_IsOrderOf Sat2.R3) ▸ IsPrimitiveRoot.orderOf _)
  | 1 => ((orderOf_of_IsOrderOf Sat2.R13) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 M := ![![0, 1], ![1, 0]]
 hM1 := by 
  intro i j hj
  fin_cases i <;> interval_cases j 
  · erw [eq_of_DiscreteLogCertificate Sat2.Log00] ; decide
  · erw [eq_of_DiscreteLogCertificate Sat2.Log10] ; decide
 hM2 := by 
  intro i 
  fin_cases i 
  · erw [eq_of_DiscreteLogCertificate Sat2.Log01] ; decide
  · erw [eq_of_DiscreteLogCertificate Sat2.Log11] ; decide
 Minv := ![![0, 1], ![1, 0]]
 hInv := by decide

lemma ne_dvd_torsion3 : ¬3 ∣ Nat.card ↥(CommGroup.torsion (↥O)ˣ) := by
 suffices ¬ 3 ∣ 2 from ?_
 · convert this
   rw [O_integral_closure, ← Fintype.card_eq_nat_card,
   ←  NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by erw [K_finrank] ; decide)]
   rfl
 · decide

def NPCU3 : pMaximalUnitsCertificateNDvdT O 3 where 
 hp := by decide
 r := 1
 huc := by 
  erw [units_finrank_of_RankUnitsCertificate RC]
  decide
 u := ![zeta1]
 hu := fun i => 
  match i with 
  | 0 => isUnit_zeta1
 t := 1
 hrle := by decide
 q := ![13]
 hqP := by 
  intro i 
  match i with 
  | 0 => exact Sat3.hq13
 I := ![Sat3.I0]
 hcard := fun i =>
  match i with  
  | 0 => Sat3.N0
 ζ := ![2]
 hr := fun i =>
  match i with 
  | 0 => ((orderOf_of_IsOrderOf Sat3.R13) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 hpndvdt := ne_dvd_torsion3
 M := ![![1]]
 hM1 := by 
  intro i j
  fin_cases i <;> fin_cases j 
  · erw [eq_of_DiscreteLogCertificate Sat3.Log00] ; decide
 Minv := ![![1]] 
 hInv := by decide

lemma ne_dvd_torsion5 : ¬5 ∣ Nat.card ↥(CommGroup.torsion (↥O)ˣ) := by
 suffices ¬ 5 ∣ 2 from ?_
 · convert this
   rw [O_integral_closure, ← Fintype.card_eq_nat_card,
   ←  NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by erw [K_finrank] ; decide)]
   rfl
 · decide

def NPCU5 : pMaximalUnitsCertificateNDvdT O 5 where 
 hp := by decide
 r := 1
 huc := by 
  erw [units_finrank_of_RankUnitsCertificate RC]
  decide
 u := ![zeta1]
 hu := fun i => 
  match i with 
  | 0 => isUnit_zeta1
 t := 1
 hrle := by decide
 q := ![131]
 hqP := by 
  intro i 
  match i with 
  | 0 => exact Sat5.hq131
 I := ![Sat5.I0]
 hcard := fun i =>
  match i with  
  | 0 => Sat5.N0
 ζ := ![2]
 hr := fun i =>
  match i with 
  | 0 => ((orderOf_of_IsOrderOf Sat5.R131) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 hpndvdt := ne_dvd_torsion5
 M := ![![4]]
 hM1 := by 
  intro i j
  fin_cases i <;> fin_cases j 
  · erw [eq_of_DiscreteLogCertificate Sat5.Log00] ; decide
 Minv := ![![4]] 
 hInv := by decide


lemma T_discr : T.discr = -15336 :=  by
  convert discriminant_eq_DiscriminantOfPRemainder_of_SturmBuilderOfList SturmRC
  rw [T_ofList]

theorem K_discr : NumberField.discr K = -1704 := by
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

end NF3_1_1704_1
