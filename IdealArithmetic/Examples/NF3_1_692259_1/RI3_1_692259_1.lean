
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_692259_1.Irreducible3_1_692259_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 + 48*X - 463
lemma T_def : T = X^3 + 48*X - 463 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-463, 48, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/3*a^2 + 1/3*a + 1/3] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 3
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![3, 0, 0], ![0, 3, 0], ![1, 1, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![-1, -1, 3],![154, -16, 1]], 
![![0, 0, 1],![154, -16, 1],![108, 46, -15]]]
 s := ![![[], [], []],![[], [], [-3]],![[], [-3], [-2, -1]]]
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
 ![[0, 1, 0], [-1, -1, 3], [154, -16, 1]], 
 ![[0, 0, 1], [154, -16, 1], [108, 46, -15]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp73: Fact $ Nat.Prime 73 := fact_iff.2 (by norm_num)
instance hp109: Fact $ Nat.Prime 109 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp29: Fact $ Nat.Prime 29 := fact_iff.2 (by norm_num)

def CD29: CertificateDedekindCriterionLists l 29 where
 n := 2
 a' := [25]
 b' := [19, 2]
 k := [9, 1]
 f := [17, 5, 1]
 g := [3, 19, 1]
 h := [10, 1]
 a := [26, 10]
 b := [27, 19]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD73: CertificateDedekindCriterionLists l 73 where
 n := 2
 a' := [71]
 b' := [54, 1]
 k := [70, 1]
 f := [23, 18, 1]
 g := [32, 35, 1]
 h := [38, 1]
 a := [32, 53]
 b := [66, 20]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD109: CertificateDedekindCriterionLists l 109 where
 n := 2
 a' := [106]
 b' := [10, 56]
 k := [63, 1]
 f := [11, 18, 1]
 g := [32, 86, 1]
 h := [23, 1]
 a := [12, 73]
 b := [47, 36]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
 n := 4
 p := ![3, 29, 73, 109]
 exp := ![3, 1, 1, 1]
 pdgood := [29, 73, 109]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp3.out
  exact hp29.out
  exact hp73.out
  exact hp109.out
 a := [-12501, -864]
 b := [9216, 4167, 288]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
  exact satisfiesDedekindCriterion_of_certificate_lists T l 73 T_ofList CD73
  exact satisfiesDedekindCriterion_of_certificate_lists T l 109 T_ofList CD109

noncomputable def M3 : MaximalOrderCertificateLists 3 O Om hm where
 m := 1
 n := 2
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 1, 0], [2, 2, 0], [1, 2, 1]], 
![[0, 0, 1], [1, 2, 1], [0, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 2, 0]]
 b2 := ![![1, 0, 0],![1, 0, 2]]
 v := ![![1, 2, 0]]
 w := ![![1, 0, 0],![1, 0, 2]]
 wFrob := ![![1, 0, 0],![0, 1, 2]]
 v_ind := ![0]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 0, 0],![0, 2, 2],![4, 2, 0]]
 a := ![![![1]],![![-33]],![![3]]]
 c := ![![![0, 0]],![![212, 3]],![![-3, 2]]]
 d := ![![![0],![0]],![![3],![183]],![![3],![-93]]]
 e := ![![![1, 0],![0, 1]],![![-2, 1],![1014, -27]],![![3, 0],![645, 6]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inl 0, Sum.inr 0),(Sum.inl 0, Sum.inr 1)]
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

