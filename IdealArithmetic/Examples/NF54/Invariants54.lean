import IdealArithmetic.Examples.NF54.NonPrincipalExample54

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
  by_cases hc : p ∈ [2, 3, 7]
  · fin_cases hc
    exact pMaximal_of_MaximalOrderCertificateWLists 2 O Om hm M2
    exact pMaximal_of_MaximalOrderCertificateWLists 3 O Om hm M3
    exact pMaximal_of_MaximalOrderCertificateOfUnramifiedLists 7 O Om hm M7
  · haveI : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T _ T_ofList [2, 3, 7] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']



--theorem O_integral_closure : O = integralClosure ℤ K := by sorry

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


def SturmRC : SturmBuilderOfList [[432, 210, -10, -15, 0, 1], [210, -20, -45, 0, 5], [-72, -28, 1, 1], [3, -4, -2], [3, 1], [1]] [432, 210, -10, -15, 0, 1] [210, -20, -45, 0, 5] where
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
  e := [25, 1, 4, 1]
  f := [150, 50, 98, 3]
  epos := by decide
  fpos := by decide
  Q := [[0, 5], [-5, 5], [2, -2], [2, -2]]
  hel := by decide
  hfl := by decide
  hQl := by decide
  hrem := by
    dsimp
    intro i hi
    have hi : i < 4 := by omega
    interval_cases i <;> (dsimp ; decide)

def RC : RankUnitsCertificate O where
  f := X^5 - 15*X^3 - 10*X^2 + 210*X + 432
  l := [432, 210, -10, -15, 0, 1]
  hl := T_ofList
  hlz := by decide
  hz := by decide
  hAdj := Adj
  heq := O_integral_closure
  P := [[432, 210, -10, -15, 0, 1], [210, -20, -45, 0, 5], [-72, -28, 1, 1], [3, -4, -2], [3, 1], [1]]
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
 q := ![31, 61, 101]
 hqP := by
  intro i
  match i with
  | 0 => exact hq31
  | 1 => exact hq61
  | 2 => exact hq101
 I := ![I0, I1, I2]
 hcard := fun i =>
  match i with
  | 0 => N0
  | 1 => N1
  | 2 => N2
 ζ := ![3, 2, 2]
 hr := fun i =>
  match i with
  | 0 => ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _)
  | 1 => ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _)
  | 2 => ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _)
 hdvd := by decide
 a := alpha
 n := 5
 hpdvd := by decide
 hJ := J5
 hpndvdt := ne_dvd_torsion5
 M := ![![2, 4, 4], ![1, 0, 0], ![4, 3, 2]]
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
 Minv := ![![0, 1, 0], ![2, 2, 1], ![2, 0, 4]]
 hInv := by decide
 N := ![![0, 1], ![4, 2]]
 hNiv := by decide

theorem J_not_principal : ¬ ∃ b, J = Ideal.span {b} :=
  not_principal_of_NonPrincipalCertificateNDvdT NPCJ
