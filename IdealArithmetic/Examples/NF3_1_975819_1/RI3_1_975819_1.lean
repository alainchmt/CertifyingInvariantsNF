
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_975819_1.Irreducible3_1_975819_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - X^2 - 195*X + 1482
lemma T_def : T = X^3 - X^2 - 195*X + 1482 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [1482, -195, -1, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/5*a^2 - 2/5*a + 2/5] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 5
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![5, 0, 0], ![0, 5, 0], ![2, -2, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![-2, 2, 5],![-296, 39, -1]], 
![![0, 0, 1],![-296, 39, -1],![162, -67, 40]]]
 s := ![![[], [], []],![[], [], [-5]],![[], [-5], [3, -1]]]
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
 ![[0, 1, 0], [-2, 2, 5], [-296, 39, -1]], 
 ![[0, 0, 1], [-296, 39, -1], [162, -67, 40]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp131: Fact $ Nat.Prime 131 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp13: Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)
instance hp191: Fact $ Nat.Prime 191 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n := 2
 a' := [2]
 b' := [2, 2]
 k := [2, 1]
 f := [-494, 65, 1]
 g := [0, 2, 1]
 h := [0, 1]
 a := [1]
 b := [2]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD13: CertificateDedekindCriterionLists l 13 where
 n := 2
 a' := [9]
 b' := [12, 2]
 k := [12, 1]
 f := [-114, 15, 1]
 g := [0, 12, 1]
 h := [0, 1]
 a := [9, 2]
 b := [11, 11]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD131: CertificateDedekindCriterionLists l 131 where
 n := 2
 a' := [76]
 b' := [117, 93]
 k := [99, 1]
 f := [6, 32, 1]
 g := [28, 49, 1]
 h := [81, 1]
 a := [44, 119]
 b := [14, 12]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD191: CertificateDedekindCriterionLists l 191 where
 n := 2
 a' := [176]
 b' := [149, 103]
 k := [55, 1]
 f := [145, 25, 1]
 g := [179, 27, 1]
 h := [163, 1]
 a := [43, 138]
 b := [42, 53]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [5] where
 n := 5
 p := ![3, 5, 13, 131, 191]
 exp := ![1, 2, 1, 1, 1]
 pdgood := [3, 13, 131, 191]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp3.out
  exact hp5.out
  exact hp13.out
  exact hp131.out
  exact hp191.out
 a := [37085, 3516]
 b := [156741, -11971, -1172]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13
  exact satisfiesDedekindCriterion_of_certificate_lists T l 131 T_ofList CD131
  exact satisfiesDedekindCriterion_of_certificate_lists T l 191 T_ofList CD191

noncomputable def M5 : MaximalOrderCertificateOfUnramifiedLists 5 O Om hm where
 n := 3
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 1, 0], [3, 2, 0], [4, 4, 4]], 
![[0, 0, 1], [4, 4, 4], [2, 3, 0]]]
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

