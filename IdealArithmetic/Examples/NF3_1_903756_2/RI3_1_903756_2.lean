
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_903756_2.Irreducible3_1_903756_2
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - X^2 - 65*X - 2001
lemma T_def : T = X^3 - X^2 - 65*X - 2001 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-2001, -65, -1, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/11*a^2 + 2/11*a - 4/11] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 11
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![11, 0, 0], ![0, 11, 0], ![-4, 2, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![4, -2, 11],![183, 5, 3]], 
![![0, 0, 1],![183, 5, 3],![85, 18, 6]]]
 s := ![![[], [], []],![[], [], [-11]],![[], [-11], [-5, -1]]]
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
 ![[0, 1, 0], [4, -2, 11], [183, 5, 3]], 
 ![[0, 0, 1], [183, 5, 3], [85, 18, 6]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)
instance hp11: Fact $ Nat.Prime 11 := fact_iff.2 (by norm_num)
instance hp53: Fact $ Nat.Prime 53 := fact_iff.2 (by norm_num)
instance hp29: Fact $ Nat.Prime 29 := fact_iff.2 (by norm_num)

def CD2: CertificateDedekindCriterionLists l 2 where
 n := 3
 a' := []
 b' := [1]
 k := [1]
 f := [1001, 33, 1]
 g := [1, 1]
 h := [1, 0, 1]
 a := [1]
 b := [0, 1]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD3: CertificateDedekindCriterionLists l 3 where
 n := 2
 a' := [2]
 b' := [1, 2]
 k := [0, 1]
 f := [667, 22, 1]
 g := [0, 1, 1]
 h := [1, 1]
 a := [1]
 b := [2]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD7: CertificateDedekindCriterionLists l 7 where
 n := 3
 a' := []
 b' := [1]
 k := [1]
 f := [287, 11, 1]
 g := [2, 1]
 h := [4, 4, 1]
 a := [5]
 b := [4, 2]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD29: CertificateDedekindCriterionLists l 29 where
 n := 2
 a' := [13]
 b' := [27, 8]
 k := [0, 1]
 f := [69, 9, 1]
 g := [0, 14, 1]
 h := [14, 1]
 a := [8, 3]
 b := [7, 26]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD53: CertificateDedekindCriterionLists l 53 where
 n := 2
 a' := [40]
 b' := [13, 33]
 k := [9, 1]
 f := [45, 5, 1]
 g := [8, 4, 1]
 h := [48, 1]
 a := [51, 37]
 b := [18, 16]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [11] where
 n := 6
 p := ![2, 3, 7, 11, 29, 53]
 exp := ![2, 1, 2, 2, 1, 1]
 pdgood := [2, 3, 7, 29, 53]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp7.out
  exact hp11.out
  exact hp29.out
  exact hp53.out
 a := [-55006, 1176]
 b := [10962, 18466, -392]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
  exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
  exact satisfiesDedekindCriterion_of_certificate_lists T l 53 T_ofList CD53

noncomputable def M11 : MaximalOrderCertificateOfUnramifiedLists 11 O Om hm where
 n := 3
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 1, 0], [4, 9, 0], [7, 5, 3]], 
![[0, 0, 1], [7, 5, 3], [8, 7, 6]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0],![0, 1, 0],![0, 0, 1]]
 wFrob := ![![1, 0, 0],![0, 1, 0],![0, 0, 1]]
 w_ind := ![0, 1, 2]
 hindw := by decide
 hwFrobComp := by decide 

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

