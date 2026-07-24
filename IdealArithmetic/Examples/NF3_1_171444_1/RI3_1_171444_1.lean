
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_171444_1.Irreducible3_1_171444_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 + 9*X - 478
lemma T_def : T = X^3 + 9*X - 478 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-478, 9, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/6*a^2 + 1/6*a - 1/3] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 6
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![6, 0, 0], ![0, 6, 0], ![-2, 1, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![2, -1, 6],![80, -2, 1]], 
![![0, 0, 1],![80, -2, 1],![26, 13, -2]]]
 s := ![![[], [], []],![[], [], [-6]],![[], [-6], [-2, -1]]]
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
 ![[0, 1, 0], [2, -1, 6], [80, -2, 1]], 
 ![[0, 0, 1], [80, -2, 1], [26, 13, -2]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)
instance hp13: Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)
instance hp157: Fact $ Nat.Prime 157 := fact_iff.2 (by norm_num)

def CD7: CertificateDedekindCriterionLists l 7 where
 n := 2
 a' := [3]
 b' := [5, 2]
 k := [3, 1]
 f := [70, 1, 1]
 g := [6, 5, 1]
 h := [2, 1]
 a := [0, 5]
 b := [6, 2]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD13: CertificateDedekindCriterionLists l 13 where
 n := 2
 a' := [4]
 b' := [7, 11]
 k := [12, 1]
 f := [40, 3, 1]
 g := [6, 6, 1]
 h := [7, 1]
 a := [0, 8]
 b := [11, 5]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD157: CertificateDedekindCriterionLists l 157 where
 n := 2
 a' := [99]
 b' := [30, 29]
 k := [107, 1]
 f := [4, 21, 1]
 g := [6, 132, 1]
 h := [25, 1]
 a := [55, 131]
 b := [42, 26]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 5
 p := ![2, 3, 7, 13, 157]
 exp := ![4, 3, 1, 1, 1]
 pdgood := [7, 13, 157]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp7.out
  exact hp13.out
  exact hp157.out
 a := [-12906, -162]
 b := [324, 4302, 54]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 7 T_ofList CD7
  exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13
  exact satisfiesDedekindCriterion_of_certificate_lists T l 157 T_ofList CD157

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
![[0, 1, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 0, 1], [0, 0, 1], [0, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 1]]
 b2 := ![![1, 0, 0],![0, 1, 0]]
 v := ![![0, 1, 1]]
 w := ![![1, 0, 0],![0, 1, 0]]
 wFrob := ![![1, 0, 0],![0, 1, 0]]
 v_ind := ![1]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 0, 0],![1, 0, 1],![0, 1, 1]]
 a := ![![![1]],![![0]],![![6]]]
 c := ![![![0, 0]],![![53, 6]],![![94, 1]]]
 d := ![![![0],![0]],![![2],![2]],![![2],![14]]]
 e := ![![![1, 0],![0, 1]],![![1, -1],![80, -2]],![![0, 0],![82, -10]]]
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
![[0, 1, 0], [2, 2, 0], [2, 1, 1]], 
![[0, 0, 1], [2, 1, 1], [2, 1, 1]]]
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
 g := ![![1, 0, 0],![4, 2, 0],![0, 2, 4]]
 a := ![![![1]],![![3]],![![-9]]]
 c := ![![![0, 0]],![![-1, 4]],![![213, 6]]]
 d := ![![![0],![0]],![![3],![-9]],![![3],![147]]]
 e := ![![![1, 0],![0, 1]],![![3, 0],![321, 6]],![![-3, 2],![483, -4]]]
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

