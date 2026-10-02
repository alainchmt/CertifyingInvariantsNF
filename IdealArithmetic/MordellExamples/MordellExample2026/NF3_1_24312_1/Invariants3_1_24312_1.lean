import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.UnitsSaturated3_1_24312_1_2
import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.UnitsSaturated3_1_24312_1_3
import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.UnitsSaturated3_1_24312_1_5
import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.UnitsSaturated3_1_24312_1_7
import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.UnitsSaturated3_1_24312_1_11
import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.UnitsSaturated3_1_24312_1_13
import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.UnitsSaturated3_1_24312_1_17
import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.UnitsSaturated3_1_24312_1_19
import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.UnitsSaturated3_1_24312_1_23
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Signature.ResultantRecursive
import IdealArithmetic.DedekindProject.Discriminant

set_option linter.all false

/- Number field `K(α)` with α root of polynomial `X^3 + 3*X - 90`. -/

/- Ring of integers with basis `[1, a, 1/3*a^2]` -/

open BigOperators Classical Matrix Polynomial Module

noncomputable section

instance hirr : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

-- Forgetful inheritance, with the helpers REDUCIBLE so that instance search (which
-- works at reducible transparency) can see that `Field.toSemiring = CommRing.toSemiring`.
@[reducible] noncomputable def K_commRing : CommRing K := inferInstance
@[reducible] noncomputable def K_field_aux : Field K := by unfold K; exact AdjoinRoot.instField

noncomputable instance K_field : Field K := { K_commRing, K_field_aux with }

instance K_numberField : NumberField K := by
  unfold K
  exact AdjoinRoot.instNumberFieldRat

--instance : Module ℚ K := Algebra.toModule
--instance : @Algebra ℤ K CommRing.toCommSemiring CommRing.toCommSemiring.toSemiring := Ring.toIntAlgebra K
--instance : @CharZero K CommRing.toCommSemiring.toNonAssocSemiring.toAddCommMonoidWithOne.toAddMonoidWithOne := charZero_of_expChar_one' K

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

def SturmRC : SturmBuilderOfList [[-90, 3, 0, 1], [3, 0, 3], [810, -18], [-218808]] [-90, 3, 0, 1] [3, 0, 3] where
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
  e := [9, 324]
  f := [1, 9]
  epos := by decide
  fpos := by decide
  Q := [[0, 3], [-2430, -54]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    dsimp
    intro i hi
    have hi : i < 2 := by omega
    interval_cases i <;> (dsimp ; decide)

def RC : RankUnitsCertificate O where
  f := X^3 + 3*X - 90
  l := [-90, 3, 0, 1]
  hl := T_ofList
  hlz := by decide
  hz := by decide
  hAdj := Adj
  heq := O_integral_closure
  P := [[-90, 3, 0, 1], [3, 0, 3], [810, -18], [-218808]]
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
 q := ![3, 3]
 hqP := by
  intro i
  match i with
  | 0 => exact Sat2.hq3
  | 1 => exact Sat2.hq3
 I := ![Sat2.I0, Sat2.I1]
 hcard := fun i =>
  match i with
  | 0 => Sat2.N0
  | 1 => Sat2.N1
 ζ := ![2, 2]
 hr := fun i =>
  match i with
  | 0 => ((orderOf_of_IsOrderOf Sat2.R3) ▸ IsPrimitiveRoot.orderOf _)
  | 1 => ((orderOf_of_IsOrderOf Sat2.R3) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 M := ![![1, 1], ![0, 1]]
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
 Minv := ![![1, 1], ![0, 1]]
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
 q := ![7]
 hqP := by
  intro i
  match i with
  | 0 => exact Sat3.hq7
 I := ![Sat3.I0]
 hcard := fun i =>
  match i with
  | 0 => Sat3.N0
 ζ := ![3]
 hr := fun i =>
  match i with
  | 0 => ((orderOf_of_IsOrderOf Sat3.R7) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 hpndvdt := ne_dvd_torsion3
 M := ![![2]]
 hM1 := by
  intro i j
  fin_cases i <;> fin_cases j
  · erw [eq_of_DiscreteLogCertificate Sat3.Log00] ; decide
 Minv := ![![2]]
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
 q := ![31]
 hqP := by
  intro i
  match i with
  | 0 => exact Sat5.hq31
 I := ![Sat5.I0]
 hcard := fun i =>
  match i with
  | 0 => Sat5.N0
 ζ := ![3]
 hr := fun i =>
  match i with
  | 0 => ((orderOf_of_IsOrderOf Sat5.R31) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 hpndvdt := ne_dvd_torsion5
 M := ![![4]]
 hM1 := by
  intro i j
  fin_cases i <;> fin_cases j
  · erw [eq_of_DiscreteLogCertificate Sat5.Log00] ; decide
 Minv := ![![4]]
 hInv := by decide

lemma ne_dvd_torsion7 : ¬7 ∣ Nat.card ↥(CommGroup.torsion (↥O)ˣ) := by
 suffices ¬ 7 ∣ 2 from ?_
 · convert this
   rw [O_integral_closure, ← Fintype.card_eq_nat_card,
   ←  NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by erw [K_finrank] ; decide)]
   rfl
 · decide

def NPCU7 : pMaximalUnitsCertificateNDvdT O 7 where
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
 q := ![29]
 hqP := by
  intro i
  match i with
  | 0 => exact Sat7.hq29
 I := ![Sat7.I0]
 hcard := fun i =>
  match i with
  | 0 => Sat7.N0
 ζ := ![2]
 hr := fun i =>
  match i with
  | 0 => ((orderOf_of_IsOrderOf Sat7.R29) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 hpndvdt := ne_dvd_torsion7
 M := ![![2]]
 hM1 := by
  intro i j
  fin_cases i <;> fin_cases j
  · erw [eq_of_DiscreteLogCertificate Sat7.Log00] ; decide
 Minv := ![![4]]
 hInv := by decide

lemma ne_dvd_torsion11 : ¬11 ∣ Nat.card ↥(CommGroup.torsion (↥O)ˣ) := by
 suffices ¬ 11 ∣ 2 from ?_
 · convert this
   rw [O_integral_closure, ← Fintype.card_eq_nat_card,
   ←  NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by erw [K_finrank] ; decide)]
   rfl
 · decide

def NPCU11 : pMaximalUnitsCertificateNDvdT O 11 where
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
 q := ![23]
 hqP := by
  intro i
  match i with
  | 0 => exact Sat11.hq23
 I := ![Sat11.I0]
 hcard := fun i =>
  match i with
  | 0 => Sat11.N0
 ζ := ![5]
 hr := fun i =>
  match i with
  | 0 => ((orderOf_of_IsOrderOf Sat11.R23) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 hpndvdt := ne_dvd_torsion11
 M := ![![1]]
 hM1 := by
  intro i j
  fin_cases i <;> fin_cases j
  · erw [eq_of_DiscreteLogCertificate Sat11.Log00] ; decide
 Minv := ![![1]]
 hInv := by decide

lemma ne_dvd_torsion13 : ¬13 ∣ Nat.card ↥(CommGroup.torsion (↥O)ˣ) := by
 suffices ¬ 13 ∣ 2 from ?_
 · convert this
   rw [O_integral_closure, ← Fintype.card_eq_nat_card,
   ←  NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by erw [K_finrank] ; decide)]
   rfl
 · decide

def NPCU13 : pMaximalUnitsCertificateNDvdT O 13 where
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
  | 0 => exact Sat13.hq131
 I := ![Sat13.I0]
 hcard := fun i =>
  match i with
  | 0 => Sat13.N0
 ζ := ![2]
 hr := fun i =>
  match i with
  | 0 => ((orderOf_of_IsOrderOf Sat13.R131) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 hpndvdt := ne_dvd_torsion13
 M := ![![9]]
 hM1 := by
  intro i j
  fin_cases i <;> fin_cases j
  · erw [eq_of_DiscreteLogCertificate Sat13.Log00] ; decide
 Minv := ![![3]]
 hInv := by decide

lemma ne_dvd_torsion17 : ¬17 ∣ Nat.card ↥(CommGroup.torsion (↥O)ˣ) := by
 suffices ¬ 17 ∣ 2 from ?_
 · convert this
   rw [O_integral_closure, ← Fintype.card_eq_nat_card,
   ←  NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by erw [K_finrank] ; decide)]
   rfl
 · decide

def NPCU17 : pMaximalUnitsCertificateNDvdT O 17 where
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
 q := ![103]
 hqP := by
  intro i
  match i with
  | 0 => exact Sat17.hq103
 I := ![Sat17.I0]
 hcard := fun i =>
  match i with
  | 0 => Sat17.N0
 ζ := ![5]
 hr := fun i =>
  match i with
  | 0 => ((orderOf_of_IsOrderOf Sat17.R103) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 hpndvdt := ne_dvd_torsion17
 M := ![![1]]
 hM1 := by
  intro i j
  fin_cases i <;> fin_cases j
  · erw [eq_of_DiscreteLogCertificate Sat17.Log00] ; decide
 Minv := ![![1]]
 hInv := by decide

lemma ne_dvd_torsion19 : ¬19 ∣ Nat.card ↥(CommGroup.torsion (↥O)ˣ) := by
 suffices ¬ 19 ∣ 2 from ?_
 · convert this
   rw [O_integral_closure, ← Fintype.card_eq_nat_card,
   ←  NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by erw [K_finrank] ; decide)]
   rfl
 · decide

def NPCU19 : pMaximalUnitsCertificateNDvdT O 19 where
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
 q := ![229]
 hqP := by
  intro i
  match i with
  | 0 => exact Sat19.hq229
 I := ![Sat19.I0]
 hcard := fun i =>
  match i with
  | 0 => Sat19.N0
 ζ := ![6]
 hr := fun i =>
  match i with
  | 0 => ((orderOf_of_IsOrderOf Sat19.R229) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 hpndvdt := ne_dvd_torsion19
 M := ![![2]]
 hM1 := by
  intro i j
  fin_cases i <;> fin_cases j
  · erw [eq_of_DiscreteLogCertificate Sat19.Log00] ; decide
 Minv := ![![10]]
 hInv := by decide

lemma ne_dvd_torsion23 : ¬23 ∣ Nat.card ↥(CommGroup.torsion (↥O)ˣ) := by
 suffices ¬ 23 ∣ 2 from ?_
 · convert this
   rw [O_integral_closure, ← Fintype.card_eq_nat_card,
   ←  NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by erw [K_finrank] ; decide)]
   rfl
 · decide

def NPCU23 : pMaximalUnitsCertificateNDvdT O 23 where
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
 q := ![47]
 hqP := by
  intro i
  match i with
  | 0 => exact Sat23.hq47
 I := ![Sat23.I0]
 hcard := fun i =>
  match i with
  | 0 => Sat23.N0
 ζ := ![5]
 hr := fun i =>
  match i with
  | 0 => ((orderOf_of_IsOrderOf Sat23.R47) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 hpndvdt := ne_dvd_torsion23
 M := ![![8]]
 hM1 := by
  intro i j
  fin_cases i <;> fin_cases j
  · erw [eq_of_DiscreteLogCertificate Sat23.Log00] ; decide
 Minv := ![![3]]
 hInv := by decide


lemma T_discr : T.discr = -218808 :=  by
  convert discriminant_eq_DiscriminantOfPRemainder_of_SturmBuilderOfList SturmRC
  rw [T_ofList]

theorem K_discr : NumberField.discr K = -24312 := by
  rw [discr_numberField_eq_discrSubalgebraBuilder T_irreducible BQ O_integral_closure]
  rw [T_discr]
  rfl

lemma K_nrComplexPlaces : NumberField.InfinitePlace.nrComplexPlaces K = 1 := by
  rw [nrComplexPlaces_of_RankUnitsCertificate RC]
  rfl

lemma K_nrRealPlaces : NumberField.InfinitePlace.nrRealPlaces K = 1 := by
  rw [nrRealPlaces_of_RankUnitsCertificate RC]
  rfl
