
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF5_3_379687500_1.Irreducible5_3_379687500_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 40*X^3 - 10*X^2 - 15*X - 8
lemma T_def : T = X^5 - 40*X^3 - 10*X^2 - 15*X - 8 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-8, -15, -10, -40, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/42*a^4 - 17/42*a^3 - 1/14*a^2 - 1/42*a + 1/21] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d := 42
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![42, 0, 0, 0, 0], ![0, 42, 0, 0, 0], ![0, 0, 42, 0, 0], ![0, 0, 0, 42, 0], ![2, -1, -3, -17, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-2, 1, 3, 17, 42],![1, 0, -1, -6, -17]], 
![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-2, 1, 3, 17, 42],![8, 15, 10, 40, 0],![-5, -5, -1, -1, 37]], 
![![0, 0, 0, 1, 0],![-2, 1, 3, 17, 42],![8, 15, 10, 40, 0],![-80, 48, 135, 690, 1680],![39, -6, -45, -240, -671]], 
![![0, 0, 0, 0, 1],![1, 0, -1, -6, -17],![-5, -5, -1, -1, 37],![39, -6, -45, -240, -671],![-20, -2, 17, 95, 301]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-42]],![[], [], [], [-1764], [714, -42]],![[], [], [-1764], [0, -1764], [-1554, 714, -42]],![[], [-42], [714, -42], [-1554, 714, -42], [1250, -323, 34, -1]]]
 h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide 

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ

noncomputable def B : Basis (Fin 5) ℤ O := timesTableO.basis
def Table : Fin 5 → Fin 5 → List ℤ := 
 ![ ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-2, 1, 3, 17, 42], [1, 0, -1, -6, -17]], 
 ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-2, 1, 3, 17, 42], [8, 15, 10, 40, 0], [-5, -5, -1, -1, 37]], 
 ![[0, 0, 0, 1, 0], [-2, 1, 3, 17, 42], [8, 15, 10, 40, 0], [-80, 48, 135, 690, 1680], [39, -6, -45, -240, -671]], 
 ![[0, 0, 0, 0, 1], [1, 0, -1, -6, -17], [-5, -5, -1, -1, 37], [39, -6, -45, -240, -671], [-20, -2, 17, 95, 301]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [2, 4, 4, 10, 1]
 g := [2, 1]
 h := [1, 2, 4, 3, 1]
 a := [1]
 b := [2, 2, 2, 4]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 7] where
 n := 4
 p := ![2, 3, 5, 7]
 exp := ![4, 7, 8, 2]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp7.out
 a := [-70470000000, 111678750000, 3695625000, -4657500000]
 b := [-7067250000, 20331000000, -37239750000, -739125000, 931500000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 2
 n := 3
 t := 3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [1, 0, 1, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 0, 0, 0], [1, 1, 1, 1, 1]], 
![[0, 0, 0, 1, 0], [0, 1, 1, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 0, 1]], 
![[0, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 1, 1, 1, 1], [1, 0, 1, 0, 1], [0, 0, 1, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1],![0, 1, 0, 0, 1]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 0, 0, 0, 1],![0, 1, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 1, 0, 1],![0, 0, 0, 1, 1]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 1, 1, 1, 1],![0, 0, 0, 1, 0],![0, 0, 1, 1, 1],![0, 1, 1, 0, 1],![1, 0, 1, 0, 0]]
 w1 := ![1, 1]
 w2 := ![0, 1, 0]
 a := ![![619, 162],![764, 193],![600, 156],![-146, -32],![76, 22]]
 c := ![![-20, 1012, -258],![-38, 1362, -332],![-19, 978, -250],![18, -351, 74],![2, 86, -27]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 2
 n := 3
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [1, 1, 0, 2, 0], [1, 0, 2, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [1, 1, 0, 2, 0], [2, 0, 1, 1, 0], [1, 1, 2, 2, 1]], 
![[0, 0, 0, 1, 0], [1, 1, 0, 2, 0], [2, 0, 1, 1, 0], [1, 0, 0, 0, 0], [0, 0, 0, 0, 1]], 
![[0, 0, 0, 0, 1], [1, 0, 2, 0, 1], [1, 1, 2, 2, 1], [0, 0, 0, 0, 1], [1, 1, 2, 2, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 2, 0, 0],![0, 1, 0, 2, 0]]
 b2 := ![![1, 0, 0, 0, 0],![1, 0, 0, 0, 2],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 2, 0, 0],![0, 1, 0, 2, 0]]
 w := ![![1, 0, 0, 0, 0],![1, 0, 0, 0, 2],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 2],![0, 0, 0, 1, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![4, 2, 0, 0, 4],![2, 2, 2, 0, 2],![2, 4, 0, 2, 4],![0, 0, 2, 0, 4],![0, 2, 0, 2, 2]]
 w1 := ![1, 1]
 w2 := ![0, 1, 0]
 a := ![![23, 168],![36, 193],![45, 207],![42, 273],![33, 123]]
 c := ![![-417, 348, -96],![-327, 273, -81],![-151, 132, -45],![-546, 452, -135],![54, -39, 1]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M7 : MaximalOrderCertificateOfUnramifiedLists 7 O Om hm where
 n := 5
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [5, 1, 3, 3, 0], [1, 0, 6, 1, 4]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [5, 1, 3, 3, 0], [1, 1, 3, 5, 0], [2, 2, 6, 6, 2]], 
![[0, 0, 0, 1, 0], [5, 1, 3, 3, 0], [1, 1, 3, 5, 0], [4, 6, 2, 4, 0], [4, 1, 4, 5, 1]], 
![[0, 0, 0, 0, 1], [1, 0, 6, 1, 4], [2, 2, 6, 6, 2], [4, 1, 4, 5, 1], [1, 5, 3, 4, 0]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![6, 1, 4, 0, 0],![4, 0, 6, 0, 0],![4, 0, 5, 1, 0],![1, 5, 4, 6, 6]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide 

open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0, 0, 0, 0] = 1 := by
  rw [Basis.equivFun_symm_eq_repr_symm']
  apply_fun B.repr
  rw [← B_one]
  simp only [Basis.repr_symm_apply, Basis.repr_linearCombination, Fin.isValue, Basis.repr_self]
  ext i
  fin_cases i <;> norm_num
  · exact LinearEquiv.injective B.repr

instance : IsDomain O := by
  haveI hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) :=
  {out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible}
  letI hola : Field K := by
    unfold K
    exact AdjoinRoot.instField
  haveI : IsDomain K := by infer_instance
  refine Subalgebra.isDomain O

 noncomputable instance : Mul (Ideal ↥O) := Submodule.mul (R := O) (A := O)
 noncomputable instance  : AddCommMonoid ↥O := AddSubmonoidClass.toAddCommMonoid O
 noncomputable instance : Module ℤ O := O.instModuleSubtypeMem
 noncomputable instance  : Algebra ℤ O := O.algebra'

