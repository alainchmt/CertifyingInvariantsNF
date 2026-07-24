
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_746956_1.Irreducible3_1_746956_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 + 238*X - 1162
lemma T_def : T = X^3 + 238*X - 1162 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-1162, 238, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/11*a^2 - 4/11*a + 1/11] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 11
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![11, 0, 0], ![0, 11, 0], ![1, -4, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![-1, 4, 11],![106, -23, -4]], 
![![0, 0, 1],![106, -23, -4],![-75, 18, -20]]]
 s := ![![[], [], []],![[], [], [-11]],![[], [-11], [8, -1]]]
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
 ![[0, 1, 0], [-1, 4, 11], [106, -23, -4]], 
 ![[0, 0, 1], [106, -23, -4], [-75, 18, -20]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp37: Fact $ Nat.Prime 37 := fact_iff.2 (by norm_num)
instance hp103: Fact $ Nat.Prime 103 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)
instance hp11: Fact $ Nat.Prime 11 := fact_iff.2 (by norm_num)

def CD2: CertificateDedekindCriterionLists l 2 where
 n := 3
 a' := []
 b' := [1]
 k := [1]
 f := [581, -119]
 g := [0, 1]
 h := [0, 0, 1]
 a := [1]
 b := [1]
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
 f := [166, -34]
 g := [0, 1]
 h := [0, 0, 1]
 a := [3]
 b := [4]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD37: CertificateDedekindCriterionLists l 37 where
 n := 2
 a' := [34]
 b' := [21, 20]
 k := [19, 1]
 f := [37, 1, 1]
 g := [23, 28, 1]
 h := [9, 1]
 a := [23, 17]
 b := [29, 20]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD103: CertificateDedekindCriterionLists l 103 where
 n := 2
 a' := [73]
 b' := [11, 15]
 k := [51, 1]
 f := [34, 18, 1]
 g := [90, 77, 1]
 h := [26, 1]
 a := [22, 65]
 b := [2, 38]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [11] where
 n := 5
 p := ![2, 7, 11, 37, 103]
 exp := ![2, 2, 2, 1, 1]
 pdgood := [2, 7, 37, 103]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp7.out
  exact hp11.out
  exact hp37.out
  exact hp103.out
 a := [-31374, -4284]
 b := [226576, 10458, 1428]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 2 T_ofList CD2
  exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
  exact satisfiesDedekindCriterion_of_certificate_lists T l 37 T_ofList CD37
  exact satisfiesDedekindCriterion_of_certificate_lists T l 103 T_ofList CD103

noncomputable def M11 : MaximalOrderCertificateOfUnramifiedLists 11 O Om hm where
 n := 3
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 1, 0], [10, 4, 0], [7, 10, 7]], 
![[0, 0, 1], [7, 10, 7], [2, 7, 2]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0],![0, 1, 0],![8, 7, 10]]
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

