
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_516660_1.Irreducible3_1_516660_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - X^2 - 180*X - 1188
lemma T_def : T = X^3 - X^2 - 180*X - 1188 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-1188, -180, -1, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/6*a^2 - 1/6*a] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 6
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![6, 0, 0], ![0, 6, 0], ![0, -1, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![0, 1, 6],![198, 30, 0]], 
![![0, 0, 1],![198, 30, 0],![-33, 33, 30]]]
 s := ![![[], [], []],![[], [], [-6]],![[], [-6], [1, -1]]]
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
 ![[0, 1, 0], [0, 1, 6], [198, 30, 0]], 
 ![[0, 0, 1], [198, 30, 0], [-33, 33, 30]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp109: Fact $ Nat.Prime 109 := fact_iff.2 (by norm_num)
instance hp79: Fact $ Nat.Prime 79 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n := 2
 a' := [1]
 b' := [3, 2]
 k := [2, 1]
 f := [238, 37, 1]
 g := [2, 3, 1]
 h := [1, 1]
 a := [4, 1]
 b := [2, 4]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD79: CertificateDedekindCriterionLists l 79 where
 n := 2
 a' := [53]
 b' := [15, 13]
 k := [36, 1]
 f := [27, 18, 1]
 g := [45, 57, 1]
 h := [21, 1]
 a := [7, 40]
 b := [52, 39]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD109: CertificateDedekindCriterionLists l 109 where
 n := 2
 a' := [1]
 b' := [42, 54]
 k := [101, 1]
 f := [54, 29, 1]
 g := [81, 50, 1]
 h := [58, 1]
 a := [91, 100]
 b := [47, 9]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 5
 p := ![2, 3, 5, 79, 109]
 exp := ![4, 3, 1, 1, 1]
 pdgood := [5, 79, 109]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp79.out
  exact hp109.out
 a := [-34780, 3246]
 b := [126216, 11954, -1082]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
  exact satisfiesDedekindCriterion_of_certificate_lists T l 79 T_ofList CD79
  exact satisfiesDedekindCriterion_of_certificate_lists T l 109 T_ofList CD109

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
 g := ![![1, 0, 0],![1, 0, 1],![0, 1, 0]]
 a := ![![![1]],![![32]],![![6]]]
 c := ![![![0, 0]],![![67, 16]],![![96, 13]]]
 d := ![![![0],![0]],![![2],![0]],![![0],![12]]]
 e := ![![![1, 0],![0, 1]],![![0, -1],![198, 31]],![![0, 1],![-6, -5]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inl 0, Sum.inr 0),(Sum.inl 0, Sum.inr 1)]
 hindab := by decide
 hmul1 := by decide
 hmul2 := by decide
            
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
![[0, 1, 0], [0, 1, 0], [0, 0, 0]], 
![[0, 0, 1], [0, 0, 0], [0, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 0, 1]]
 b2 := ![![1, 0, 0],![0, 1, 0]]
 v := ![![0, 0, 1]]
 w := ![![1, 0, 0],![0, 1, 0]]
 wFrob := ![![1, 0, 0],![0, 1, 0]]
 v_ind := ![2]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 0, 0],![0, 1, 1],![0, 1, 0]]
 a := ![![![1]],![![30]],![![0]]]
 c := ![![![0, 0]],![![55, 21]],![![66, 10]]]
 d := ![![![0],![0]],![![3],![18]],![![0],![18]]]
 e := ![![![1, 0],![0, 1]],![![0, 1],![198, 31]],![![0, 1],![0, 1]]]
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

