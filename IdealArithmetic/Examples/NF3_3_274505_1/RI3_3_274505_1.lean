
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_3_274505_1.Irreducible3_3_274505_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - X^2 - 56*X - 109
lemma T_def : T = X^3 - X^2 - 56*X - 109 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-109, -56, -1, 1]

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
![![0, 1, 0],![0, 0, 1],![109, 56, 1]], 
![![0, 0, 1],![109, 56, 1],![109, 165, 57]]]
 s := ![![[], [], []],![[], [], [-1]],![[], [-1], [-1, -1]]]
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
 ![[0, 1, 0], [0, 0, 1], [109, 56, 1]], 
 ![[0, 0, 1], [109, 56, 1], [109, 165, 57]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)
instance hp11: Fact $ Nat.Prime 11 := fact_iff.2 (by norm_num)
instance hp23: Fact $ Nat.Prime 23 := fact_iff.2 (by norm_num)
instance hp31: Fact $ Nat.Prime 31 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n := 2
 a' := [4]
 b' := [0, 3]
 k := [1, 1]
 f := [25, 12, 1]
 g := [4, 0, 1]
 h := [4, 1]
 a := [3, 4]
 b := [4, 1]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD7: CertificateDedekindCriterionLists l 7 where
 n := 2
 a' := [3]
 b' := [2, 2]
 k := [5, 1]
 f := [19, 10, 1]
 g := [6, 2, 1]
 h := [4, 1]
 a := [2, 3]
 b := [2, 4]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD11: CertificateDedekindCriterionLists l 11 where
 n := 2
 a' := [10]
 b' := [0, 6]
 k := [1, 1]
 f := [19, 6, 1]
 g := [10, 0, 1]
 h := [10, 1]
 a := [9, 5]
 b := [5, 6]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD23: CertificateDedekindCriterionLists l 23 where
 n := 2
 a' := [11]
 b' := [11, 6]
 k := [16, 1]
 f := [5, 5, 1]
 g := [2, 19, 1]
 h := [3, 1]
 a := [13, 20]
 b := [14, 3]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD31: CertificateDedekindCriterionLists l 31 where
 n := 2
 a' := [13]
 b' := [1, 9]
 k := [29, 1]
 f := [19, 10, 1]
 g := [30, 14, 1]
 h := [16, 1]
 a := [28, 8]
 b := [4, 23]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
 n := 5
 p := ![5, 7, 11, 23, 31]
 exp := ![1, 1, 1, 1, 1]
 pdgood := [5, 7, 11, 23, 31]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp5.out
  exact hp7.out
  exact hp11.out
  exact hp23.out
  exact hp31.out
 a := [3787, -1014]
 b := [-12273, -1375, 338]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
  exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
  exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
  exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
  exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31


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

