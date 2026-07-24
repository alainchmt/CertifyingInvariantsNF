
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_323175_1.Irreducible3_1_323175_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - X^2 - 58*X - 1088
lemma T_def : T = X^3 - X^2 - 58*X - 1088 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-1088, -58, -1, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/10*a^2 + 1/10*a + 2/5] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 10
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![10, 0, 0], ![0, 10, 0], ![4, 1, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![-4, -1, 10],![108, 6, 2]], 
![![0, 0, 1],![108, 6, 2],![30, 12, 7]]]
 s := ![![[], [], []],![[], [], [-10]],![[], [-10], [-3, -1]]]
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
 ![[0, 1, 0], [-4, -1, 10], [108, 6, 2]], 
 ![[0, 0, 1], [108, 6, 2], [30, 12, 7]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp139: Fact $ Nat.Prime 139 := fact_iff.2 (by norm_num)
instance hp31: Fact $ Nat.Prime 31 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n := 2
 a' := [2]
 b' := [0, 2]
 k := [1, 1]
 f := [364, 20, 1]
 g := [2, 0, 1]
 h := [2, 1]
 a := [1]
 b := [2]
 c := [1]
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD31: CertificateDedekindCriterionLists l 31 where
 n := 2
 a' := [6]
 b' := [26, 28]
 k := [18, 1]
 f := [38, 7, 1]
 g := [15, 24, 1]
 h := [6, 1]
 a := [8, 27]
 b := [17, 4]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD139: CertificateDedekindCriterionLists l 139 where
 n := 2
 a' := [108]
 b' := [72, 85]
 k := [42, 1]
 f := [32, 32, 1]
 g := [70, 90, 1]
 h := [48, 1]
 a := [69, 124]
 b := [34, 15]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 5] where
 n := 5
 p := ![2, 3, 5, 31, 139]
 exp := ![2, 1, 4, 1, 1]
 pdgood := [3, 31, 139]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp31.out
  exact hp139.out
 a := [-30250, 1050]
 b := [10250, 10200, -350]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
  exact satisfiesDedekindCriterion_of_certificate_lists T l 139 T_ofList CD139

noncomputable def M2 : MaximalOrderCertificateOfUnramifiedLists 2 O Om hm where
 n := 3
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 1, 0], [0, 1, 0], [0, 0, 0]], 
![[0, 0, 1], [0, 0, 0], [0, 0, 1]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0],![0, 1, 0],![0, 0, 1]]
 wFrob := ![![1, 0, 0],![0, 1, 0],![0, 0, 1]]
 w_ind := ![0, 1, 2]
 hindw := by decide
 hwFrobComp := by decide 
noncomputable def M5 : MaximalOrderCertificateLists 5 O Om hm where
 m := 2
 n := 1
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 1, 0], [1, 4, 0], [3, 1, 2]], 
![[0, 0, 1], [3, 1, 2], [0, 2, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 4],![0, 1, 3]]
 b2 := ![![1, 0, 0]]
 v := ![![1, 0, 4],![0, 1, 3]]
 w := ![![1, 0, 0]]
 wFrob := ![![1, 0, 0]]
 v_ind := ![0, 1]
 w_ind := ![0]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 0, 0],![16, 12, 8],![12, 4, 0]]
 a := ![![![1, 0],![0, 1]],![![-415, 684],![-311, 556]],![![-55, 100],![-35, 80]]]
 c := ![![![0],![0]],![![1315],![1147]],![![359],![263]]]
 d := ![![![0, 0]],![![-35, 60]],![![-15, 20]]]
 e := ![![![1]],![![23]],![![15]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inl 1, Sum.inl 0),(Sum.inl 0, Sum.inr 0)]
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

