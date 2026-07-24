
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_959928_1.Irreducible3_1_959928_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - X^2 - 96*X - 492
lemma T_def : T = X^3 - X^2 - 96*X - 492 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-492, -96, -1, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/2*a^2 - 1/2*a] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 2
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![2, 0, 0], ![0, 2, 0], ![0, -1, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![0, 1, 2],![246, 48, 0]], 
![![0, 0, 1],![246, 48, 0],![-123, 123, 48]]]
 s := ![![[], [], []],![[], [], [-2]],![[], [-2], [1, -1]]]
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
 ![[0, 1, 0], [0, 1, 2], [246, 48, 0]], 
 ![[0, 0, 1], [246, 48, 0], [-123, 123, 48]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp37: Fact $ Nat.Prime 37 := fact_iff.2 (by norm_num)
instance hp47: Fact $ Nat.Prime 47 := fact_iff.2 (by norm_num)
instance hp23: Fact $ Nat.Prime 23 := fact_iff.2 (by norm_num)

def CD3: CertificateDedekindCriterionLists l 3 where
 n := 2
 a' := [2]
 b' := [2, 2]
 k := [2, 1]
 f := [164, 32, 1]
 g := [0, 2, 1]
 h := [0, 1]
 a := [2]
 b := [1]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD23: CertificateDedekindCriterionLists l 23 where
 n := 2
 a' := [5]
 b' := [6, 9]
 k := [19, 1]
 f := [31, 10, 1]
 g := [17, 9, 1]
 h := [13, 1]
 a := [22, 14]
 b := [10, 9]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD37: CertificateDedekindCriterionLists l 37 where
 n := 2
 a' := [27]
 b' := [31, 5]
 k := [11, 1]
 f := [20, 7, 1]
 g := [8, 5, 1]
 h := [31, 1]
 a := [4, 33]
 b := [4, 4]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD47: CertificateDedekindCriterionLists l 47 where
 n := 2
 a' := [33]
 b' := [17, 7]
 k := [4, 1]
 f := [27, 14, 1]
 g := [37, 25, 1]
 h := [21, 1]
 a := [42, 6]
 b := [24, 41]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 5
 p := ![2, 3, 23, 37, 47]
 exp := ![5, 1, 1, 1, 1]
 pdgood := [3, 23, 37, 47]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp23.out
  exact hp37.out
  exact hp47.out
 a := [-14728, 1734]
 b := [35484, 5102, -578]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 3 T_ofList CD3
  exact satisfiesDedekindCriterion_of_certificate_lists T l 23 T_ofList CD23
  exact satisfiesDedekindCriterion_of_certificate_lists T l 37 T_ofList CD37
  exact satisfiesDedekindCriterion_of_certificate_lists T l 47 T_ofList CD47

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
 m := 1
 n := 2
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 1, 0], [0, 1, 0], [0, 0, 0]], 
![[0, 0, 1], [0, 0, 0], [1, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 1, 1]]
 b2 := ![![1, 0, 0],![0, 1, 0]]
 v := ![![1, 1, 1]]
 w := ![![1, 0, 0],![0, 1, 0]]
 wFrob := ![![1, 0, 0],![0, 1, 0]]
 v_ind := ![0]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 0, 0],![1, 1, 1],![0, 1, 0]]
 a := ![![![1]],![![52]],![![2]]]
 c := ![![![0, 0]],![![159, 85]],![![122, 24]]]
 d := ![![![0],![0]],![![2],![4]],![![0],![4]]]
 e := ![![![1, 0],![0, 1]],![![0, 0],![244, 48]],![![0, 1],![-2, -1]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inl 0, Sum.inr 0),(Sum.inr 0, Sum.inr 1)]
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

