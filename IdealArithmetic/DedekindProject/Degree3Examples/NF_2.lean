
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.DedekindProject.Degree3Examples.Irreducible2
import IdealArithmetic.DedekindProject.Discriminant

-- Number field with label 3.1.6075.1 in the LMFDB

open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - 45
lemma T_def : T = X^3 - 45 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

noncomputable instance : IsScalarTower ℤ ℚ K :=
  IsScalarTower.of_algebraMap_eq (congrFun rfl)

local notation "l" => [-45, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/3*a^2] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 3
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![3, 0, 0], ![0, 3, 0], ![0, 0, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![0, 0, 3],![15, 0, 0]], 
![![0, 0, 1],![15, 0, 0],![0, 5, 0]]]
 s := ![![[], [], []],![[], [], [-3]],![[], [-3], [0, -1]]]
 h := Adj
 honed := by decide +kernel
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide +kernel 

lemma T_degree : T.natDegree = 3 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

theorem hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin 3) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 3) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ

noncomputable def B : Basis (Fin 3) ℤ O := timesTableO.basis
def Table : Fin 3 → Fin 3 → List ℤ := 
 ![ ![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
 ![[0, 1, 0], [0, 0, 3], [15, 0, 0]], 
 ![[0, 0, 1], [15, 0, 0], [0, 5, 0]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n := 3
 a' := []
 b' := [1]
 k := [1]
 f := [9]
 g := [0, 1]
 h := [0, 0, 1]
 a := [4]
 b := []
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
 n := 2
 p := ![3, 5]
 exp := ![7, 2]
 pdgood := [5]
 hsub := by decide +kernel
 hp := by
  intro i ; fin_cases i
  exact hp3.out
  exact hp5.out
 a := [-1215]
 b := [0, 405]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
 m := 2
 n := 1
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 1, 0], [0, 0, 0], [0, 0, 0]], 
![[0, 0, 1], [0, 0, 0], [0, 2, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0],![0, 0, 1]]
 b2 := ![![1, 0, 0]]
 v := ![![0, 1, 0],![0, 0, 1]]
 w := ![![1, 0, 0]]
 wFrob := ![![1, 0, 0]]
 v_ind := ![1, 2]
 w_ind := ![0]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide +kernel
 hwFrobComp := by decide +kernel 
 g := ![![1, 0, 0],![0, 0, 2],![0, 2, 0]]
 a := ![![![1, 0],![0, 1]],![![0, 0],![10, 0]],![![0, 6],![0, 0]]]
 c := ![![![0],![0]],![![10],![0]],![![0],![10]]]
 d := ![![![0, 0]],![![0, 6]],![![6, 0]]]
 e := ![![![1]],![![0]],![![0]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inl 1, Sum.inl 0),(Sum.inl 1, Sum.inr 0)]
 hindab := by decide +kernel
 hmul1 := by decide +kernel
 hmul2 := by decide +kernel
            

instance hirr : Fact $ (Irreducible (map (algebraMap ℤ ℚ) T)) where
 out :=  (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible

noncomputable instance K_field : Field K := by
  unfold K
  exact AdjoinRoot.instField

instance K_numberField : NumberField K := by
  unfold K
  exact AdjoinRoot.instNumberFieldRat

theorem O_ringOfIntegers : O = integralClosure ℤ K := by
  refine eq_of_piMaximal_at_all_primes_int O Om hm ?_
  intro p hp
  by_cases hc : p ∈ [3]
  · fin_cases hc
    exact @pMaximal_of_MaximalOrderCertificateLists K 3 _ HasUniqueDiv.to_noZeroSMulDivisors_int _ O Om hm _ _ M3
  · have : Fact $ Nat.Prime p := fact_iff.2 hp
    refine piMaximal_of_root_in_order_of_satisfiesDedekindCriterion_int Adj T_monic hm ?_ hroot_mem
     (satisfiesDedekindAlmostAllLists_of_certificate T _ T_ofList [3] D p hp hc)
    rw [T_degree, rank_subalgebra_eq_card_basis Om B']

theorem  O_ringOfIntegers' : O = NumberField.RingOfIntegers K := by rw [O_ringOfIntegers] ; rfl

lemma T_discr : T.discr = -54675 :=  by
  rw [Monic.discr_def T T_monic, T_degree, ← T_ofList]
  have : [-45, 0, 0, 1].derivative = [0, 0, 3, 0] := rfl
  rw [← ofList_derivative_eq_derivative , this]
  decide +kernel

theorem K_discr : NumberField.discr K = -6075 := by
  rw [discr_numberField_eq_discrSubalgebraBuilder T_irreducible BQ O_ringOfIntegers]
  rw [T_discr]
  rfl
