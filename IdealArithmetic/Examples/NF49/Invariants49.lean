import IdealArithmetic.Examples.NF49.NonPrincipalExample49
import Mathlib.NumberTheory.NumberField.ClassNumber
import IdealArithmetic.ResultantRecursive
import IdealArithmetic.DiscriminantSubalgebraBuilder

open BigOperators Classical Matrix Polynomial

noncomputable section

instance hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) where
  out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

noncomputable instance K_field : Field K := by
  unfold K
  infer_instance

instance K_numberField : NumberField K := by
  unfold K
  infer_instance

lemma K_finrank : Module.finrank ℚ K = 5 := by
  unfold K
  rw [Module.finrank_eq_card_basis (AdjoinRoot.powerBasisAux _), Polynomial.natDegree_map_eq_of_injective, T_degree]
  · simp
  · exact RingHom.injective_int (algebraMap ℤ ℚ)
  · exact Irreducible.ne_zero hirr.out

theorem O_integral_closure : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [2, 3]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T _ T_ofList [2, 3] D p hp hc)
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


def SturmRC : SturmBuilderOfList [[-24, 60, -70, 15, 0, 1], [60, -140, 45, 0, 5], [4, -8, 7, -1], [-4, 8, -5], [2, -9], [1]] [-24, 60, -70, 15, 0, 1] [60, -140, 45, 0, 5] where
  hlen := by decide
  h0 := by decide
  h1 := by decide
  hlast := by decide
  hdrop := by decide
  hmono := by
    dsimp
    intro i hic
    have hi : i < 5 := by omega
    interval_cases i <;> (dsimp ; decide)
  e := [25, 1, 25, 81]
  f := [150, 50, 4, 200]
  epos := by decide
  fpos := by decide
  Q := [[0, 5], [-35, -5], [-27, 5], [-62, 45]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    dsimp
    intro i hi
    have hi : i < 4 := by omega
    interval_cases i <;> (dsimp ; decide)

def RC : RankUnitsCertificate O where
  f := X^5 + 15*X^3 - 70*X^2 + 60*X - 24
  l := [-24, 60, -70, 15, 0, 1]
  hl := T_ofList
  hlz := by decide
  hz := by decide
  hAdj := Adj
  heq := O_integral_closure
  P := [[-24, 60, -70, 15, 0, 1], [60, -140, 45, 0, 5], [4, -8, 7, -1], [-4, 8, -5], [2, -9], [1]]
  SB := SturmRC
  k := 1
  r := 3
  hr := by decide
  hreq := by decide

lemma ne_dvd_torsion5 : ¬5 ∣ Nat.card ↥(CommGroup.torsion (↥O)ˣ) := by
 suffices ¬ 5 ∣ 2 from ?_
 · convert this
   rw [O_integral_closure, ← Fintype.card_eq_nat_card,
   ←  NumberField.Units.torsionOrder_eq_two_of_odd_finrank (by rw [K_finrank] ; decide)]
   rfl
 · decide

def NPCJ : NonPrincipalCertificateNDvdT J where
 p := 5
 hp := by decide
 r := 2
 huc := by
  rw [units_finrank_of_RankUnitsCertificate RC]
  decide
 u := ![zeta1, zeta2]
 hu := fun i =>
  match i with
  | 0 => isUnit_zeta1
  | 1 => isUnit_zeta2
 q := ![41, 61, 71]
 hqP := by
  intro i
  match i with
  | 0 => exact hq41
  | 1 => exact hq61
  | 2 => exact hq71
 I := ![I0, I1, I2]
 hcard := fun i =>
  match i with
  | 0 => N0
  | 1 => N1
  | 2 => N2
 ζ := ![6, 2, 7]
 hr := fun i =>
  match i with
  | 0 => ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _)
  | 1 => ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _)
  | 2 => ((orderOf_of_IsOrderOf R71) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 a := alpha
 n := 5
 hpdvd := by decide
 hJ := J5
 hpndvdt := ne_dvd_torsion5
 M := ![![0, 2, 3], ![4, 1, 3], ![0, 1, 1]]
 hM1 := by
  intro j i hj
  fin_cases i <;> interval_cases j
  · erw [eq_of_DiscreteLogCertificate Log00] ; decide
  · erw [eq_of_DiscreteLogCertificate Log01] ; decide
  · erw [eq_of_DiscreteLogCertificate Log10] ; decide
  · erw [eq_of_DiscreteLogCertificate Log11] ; decide
  · erw [eq_of_DiscreteLogCertificate Log20] ; decide
  · erw [eq_of_DiscreteLogCertificate Log21] ; decide
 hM2 := by
  intro i
  match i with
  | 0 => exact Log02
  | 1 => exact Log12
  | 2 => exact Log22
 hDl := by decide
 Minv := ![![2, 4, 2], ![4, 0, 3], ![1, 0, 3]]
 hInv := by decide
 N := ![![3, 4], ![3, 0]]
 hNiv := by decide

theorem J_not_principal : ¬ ∃ b, J = Ideal.span {b} :=
  not_principal_of_NonPrincipalCertificateNDvdT NPCJ

instance DD : IsDedekindDomainInv O := by
  rw [← isDedekindDomain_iff_isDedekindDomainInv, O_integral_closure]
  exact integralClosure.isDedekindDomain ℤ ℚ K

instance : Algebra (↥O) (FractionRing ↥O) := by
  exact OreLocalization.instAlgebra

--theorem ClassGroup.congr (R S : Type*) [CommRing R] [CommRing S] [IsDomain R] [IsDomain S]
--  (equiv : R ≃+* S) : ClassGroup R ≃* ClassGroup S := by


lemma class_group_eq : ClassGroup (NumberField.RingOfIntegers K) = ClassGroup O := by
  congr
  · exact O_ringOfIntegers'.symm
  · rw [O_integral_closure] ; rfl
  · exact proof_irrel_heq _ instIsDomainSubtypeKMemSubalgebraIntO


theorem five_dvd_class_number : 5 ∣ NumberField.classNumber K := by
  have JIsUnit := by
    refine IsDedekindDomainInv.isUnit (K := FractionRing O) DD (I := ↑J) ?_
    simp only [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
    intro hc
    rw [← Ideal.span_zero] at hc
    exact J_not_principal ⟨0 ,hc⟩
  have heqJ : (↑(IsUnit.unit JIsUnit) : FractionalIdeal (nonZeroDivisors ↥O) (FractionRing ↥O)) = ↑J := by
    rfl
  have heqJ5 : (↑((IsUnit.unit JIsUnit) ^ 5) : FractionalIdeal (nonZeroDivisors ↥O) (FractionRing ↥O)) = ↑(J ^ 5) := by
    simp only [Units.val_pow_eq_pow_val, IsUnit.unit_spec, FractionalIdeal.coeIdeal_pow]
  have horder : orderOf (ClassGroup.mk (IsUnit.unit JIsUnit) ) = 5 := by
    rw [orderOf_eq_prime_iff]
    constructor
    · rw [← map_pow, ClassGroup.mk_eq_one_of_coe_ideal heqJ5]
      use alpha
      constructor
      · unfold alpha
        refine (LinearEquiv.map_ne_zero_iff B.equivFun.symm).mpr ?_
        decide
      · exact J5
    · intro hc
      rw [ClassGroup.mk_eq_one_of_coe_ideal heqJ] at hc
      obtain ⟨x, hx, hxx⟩ := hc
      exact J_not_principal ⟨x, hxx⟩
  unfold NumberField.classNumber
  haveI : Fintype (ClassGroup O) := by
    rw [← class_group_eq]
    infer_instance
  simp_rw [class_group_eq]
  rw [← horder]
  exact orderOf_dvd_card


--#print axioms five_dvd_class_number

theorem T_discr : discriminant T = 518400000000 := by
  convert discriminant_eq_DiscriminantOfPRemainder_of_SturmBuilderOfList SturmRC
  rw [T_ofList]

theorem K_discr : NumberField.discr K = 225000000 := by
  rw [discr_numberField_eq_discrSubalgebraBuilder T_irreducible BQ O_integral_closure]
  rw [T_discr]
  rfl

lemma K_nrComplexPlaces : NumberField.InfinitePlace.nrComplexPlaces K = 2 := by
  rw [nrComplexPlaces_of_RankUnitsCertificate RC]
  rfl

theorem K_minowski (C : ClassGroup (NumberField.RingOfIntegers K)) :
  ∃ (I : (nonZeroDivisors (Ideal (NumberField.RingOfIntegers K)))),
    ClassGroup.mk0 I = C ∧
    ↑(Ideal.absNorm (↑I : Ideal (NumberField.RingOfIntegers K)) ) ≤ (933.78 : ℝ) := by
  obtain ⟨I, hI1, hI2⟩ := NumberField.exists_ideal_in_class_of_norm_le (K := K) C
  use I
  refine ⟨hI1, ?_ ⟩
  · refine le_trans hI2 ?_
    rw [K_nrComplexPlaces, K_discr, K_finrank]
    norm_num
    have := Real.pi_gt_d20
    have : (4 / Real.pi) ^ 2 < (4 / 3.14159265358979323846) ^ 2 := by
      refine (sq_lt_sq₀ ?_ ?_).mpr ?_
      · refine div_nonneg (by norm_num) (by exact Real.pi_nonneg)
      · refine div_nonneg (by norm_num) (by norm_num)
      · refine div_lt_div_of_pos_left (by norm_num) (by norm_num) this
    nlinarith
