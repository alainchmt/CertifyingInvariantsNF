
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_420812_2.Irreducible3_1_420812_2
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - X^2 + 75*X + 1
lemma T_def : T = X^3 - X^2 + 75*X + 1 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [1, 75, -1, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/2*a^2 - 1/2] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 2
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![2, 0, 0], ![0, 2, 0], ![-1, 0, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![1, 0, 2],![0, -38, 1]], 
![![0, 0, 1],![0, -38, 1],![-19, -19, -38]]]
 s := ![![[], [], []],![[], [], [-2]],![[], [-2], [-1, -1]]]
 h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide 

lemma T_degree : T.natDegree = 3 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

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
 ![[0, 1, 0], [1, 0, 2], [0, -38, 1]], 
 ![[0, 0, 1], [0, -38, 1], [-19, -19, -38]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp113: Fact $ Nat.Prime 113 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp19: Fact $ Nat.Prime 19 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def CD7: CertificateDedekindCriterionLists l 7 where
 n := 3
 a' := []
 b' := [1]
 k := [1]
 f := [1, -9, 1]
 g := [2, 1]
 h := [4, 4, 1]
 a := [4]
 b := [2, 3]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD19: CertificateDedekindCriterionLists l 19 where
 n := 2
 a' := [18]
 b' := [0, 10]
 k := [1, 1]
 f := [17, -3, 1]
 g := [18, 0, 1]
 h := [18, 1]
 a := [12, 2]
 b := [13, 17]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD113: CertificateDedekindCriterionLists l 113 where
 n := 2
 a' := [111]
 b' := [10, 1]
 k := [41, 1]
 f := [35, 16, 1]
 g := [43, 20, 1]
 h := [92, 1]
 a := [41, 109]
 b := [56, 4]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 4
 p := ![2, 7, 19, 113]
 exp := ![4, 2, 1, 1]
 pdgood := [7, 19, 113]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp7.out
  exact hp19.out
  exact hp113.out
 a := [1148, -1344]
 b := [22428, -532, 448]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
  exact satisfiesDedekindCriterion_of_certificate_lists T l 19 T_ofList CD19
  exact satisfiesDedekindCriterion_of_certificate_lists T l 113 T_ofList CD113

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
 m := 2
 n := 1
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 1, 0], [1, 0, 0], [0, 0, 1]], 
![[0, 0, 1], [0, 0, 1], [1, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 1, 0],![0, 0, 1]]
 b2 := ![![1, 0, 0]]
 v := ![![1, 1, 0],![0, 0, 1]]
 w := ![![1, 0, 0]]
 wFrob := ![![1, 0, 0]]
 v_ind := ![0, 2]
 w_ind := ![0]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 0, 0],![0, 0, 1],![1, 1, 0]]
 a := ![![![1, 0],![0, 1]],![![-38, 2],![-19, -38]],![![2, 2],![-38, 2]]]
 c := ![![![0],![0]],![![19],![0]],![![0],![19]]]
 d := ![![![0, 0]],![![0, 2]],![![2, 0]]]
 e := ![![![1]],![![0]],![![0]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inl 1, Sum.inl 0),(Sum.inl 1, Sum.inr 0)]
 hindab := by decide
 hmul1 := by decide
 hmul2 := by decide
            

open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0, 0] = 1 := by
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

