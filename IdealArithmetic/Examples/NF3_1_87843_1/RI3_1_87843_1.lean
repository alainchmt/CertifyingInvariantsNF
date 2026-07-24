
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_87843_1.Irreducible3_1_87843_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - X^2 + 27*X - 30
lemma T_def : T = X^3 - X^2 + 27*X - 30 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-30, 27, -1, 1]

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
![![0, 1, 0],![0, 0, 1],![30, -27, 1]], 
![![0, 0, 1],![30, -27, 1],![30, 3, -26]]]
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
 ![[0, 1, 0], [0, 0, 1], [30, -27, 1]], 
 ![[0, 0, 1], [30, -27, 1], [30, 3, -26]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp89: Fact $ Nat.Prime 89 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp47: Fact $ Nat.Prime 47 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n := 2
 a' := [2]
 b' := [2, 2]
 k := [2, 1]
 f := [10, -9, 1]
 g := [0, 2, 1]
 h := [0, 1]
 a := [1, 1]
 b := [1, 2]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD7: CertificateDedekindCriterionLists l 7 where
 n := 2
 a' := [6]
 b' := [2, 4]
 k := [3, 1]
 f := [5, -3, 1]
 g := [1, 1, 1]
 h := [5, 1]
 a := [6, 3]
 b := [6, 4]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD47: CertificateDedekindCriterionLists l 47 where
 n := 2
 a' := [40]
 b' := [33, 27]
 k := [32, 1]
 f := [6, 6, 1]
 g := [36, 39, 1]
 h := [7, 1]
 a := [20, 39]
 b := [45, 8]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD89: CertificateDedekindCriterionLists l 89 where
 n := 2
 a' := [49]
 b' := [33, 20]
 k := [61, 1]
 f := [44, 20, 1]
 g := [67, 30, 1]
 h := [58, 1]
 a := [26, 26]
 b := [56, 63]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [] where
 n := 4
 p := ![3, 7, 47, 89]
 exp := ![1, 1, 1, 1]
 pdgood := [3, 7, 47, 89]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp3.out
  exact hp7.out
  exact hp47.out
  exact hp89.out
 a := [-409, -480]
 b := [2799, 83, 160]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
  exact satisfiesDedekindCriterion_of_certificate_lists T l 47 T_ofList CD47
  exact satisfiesDedekindCriterion_of_certificate_lists T l 89 T_ofList CD89


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

