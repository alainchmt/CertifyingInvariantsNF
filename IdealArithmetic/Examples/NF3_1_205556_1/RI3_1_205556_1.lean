
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_205556_1.Irreducible3_1_205556_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - 79*X - 284
lemma T_def : T = X^3 - 79*X - 284 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-284, -79, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, a^2] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 1
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![0, 0, 1],![284, 79, 0]], 
![![0, 0, 1],![284, 79, 0],![0, 284, 79]]]
 s := ![![[], [], []],![[], [], [-1]],![[], [-1], [0, -1]]]
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
 ![[0, 1, 0], [0, 0, 1], [284, 79, 0]], 
 ![[0, 0, 1], [284, 79, 0], [0, 284, 79]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp67: Fact $ Nat.Prime 67 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp59: Fact $ Nat.Prime 59 := fact_iff.2 (by norm_num)
instance hp13: Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)

def CD2: CertificateDedekindCriterionLists l 2 where
 n := 2
 a' := []
 b' := [1]
 k := [0, 1]
 f := [142, 40, 1]
 g := [0, 1, 1]
 h := [1, 1]
 a := [1]
 b := [1]
 c := [1]
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD13: CertificateDedekindCriterionLists l 13 where
 n := 2
 a' := [3]
 b' := [1, 5]
 k := [6, 1]
 f := [28, 9, 1]
 g := [8, 3, 1]
 h := [10, 1]
 a := [5, 11]
 b := [7, 2]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD59: CertificateDedekindCriterionLists l 59 where
 n := 2
 a' := [55]
 b' := [20, 2]
 k := [40, 1]
 f := [22, 15, 1]
 g := [26, 20, 1]
 h := [39, 1]
 a := [15, 10]
 b := [35, 49]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD67: CertificateDedekindCriterionLists l 67 where
 n := 2
 a' := [52]
 b' := [26, 41]
 k := [63, 1]
 f := [6, 4, 1]
 g := [59, 65, 1]
 h := [2, 1]
 a := [55, 44]
 b := [16, 23]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
 n := 4
 p := ![2, 13, 59, 67]
 exp := ![2, 1, 1, 1]
 pdgood := [2, 13, 59, 67]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp13.out
  exact hp59.out
  exact hp67.out
 a := [-7668, 1422]
 b := [24964, 2556, -474]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
  exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13
  exact satisfiesDedekindCriterion_of_certificate_lists T l 59 T_ofList CD59
  exact satisfiesDedekindCriterion_of_certificate_lists T l 67 T_ofList CD67


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

