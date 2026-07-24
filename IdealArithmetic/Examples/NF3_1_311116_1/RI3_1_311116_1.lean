
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_311116_1.Irreducible3_1_311116_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - X^2 + 31*X - 651
lemma T_def : T = X^3 - X^2 + 31*X - 651 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-651, 31, -1, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/6*a^2 - 1/3*a - 1/2] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 6
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![6, 0, 0], ![0, 6, 0], ![-3, -2, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![3, 2, 6],![108, -6, -1]], 
![![0, 0, 1],![108, -6, -1],![-57, 19, -6]]]
 s := ![![[], [], []],![[], [], [-6]],![[], [-6], [3, -1]]]
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
 ![[0, 1, 0], [3, 2, 6], [108, -6, -1]], 
 ![[0, 0, 1], [108, -6, -1], [-57, 19, -6]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp193: Fact $ Nat.Prime 193 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp13: Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)
instance hp31: Fact $ Nat.Prime 31 := fact_iff.2 (by norm_num)

def CD13: CertificateDedekindCriterionLists l 13 where
 n := 2
 a' := [4]
 b' := [12, 11]
 k := [3, 1]
 f := [56, -1, 1]
 g := [7, 1, 1]
 h := [11, 1]
 a := [5, 3]
 b := [1, 10]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD31: CertificateDedekindCriterionLists l 31 where
 n := 2
 a' := [27]
 b' := [30, 2]
 k := [30, 1]
 f := [21, -1, 1]
 g := [0, 30, 1]
 h := [0, 1]
 a := [3]
 b := [28]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD193: CertificateDedekindCriterionLists l 193 where
 n := 2
 a' := [42]
 b' := [87, 172]
 k := [12, 1]
 f := [57, 48, 1]
 g := [115, 102, 1]
 h := [90, 1]
 a := [70, 57]
 b := [113, 136]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 5
 p := ![2, 3, 13, 31, 193]
 exp := ![4, 2, 1, 1, 1]
 pdgood := [13, 31, 193]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp13.out
  exact hp31.out
  exact hp193.out
 a := [-17116, -552]
 b := [1860, 5644, 184]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 13 T_ofList CD13
  exact satisfiesDedekindCriterion_of_certificate_lists T l 31 T_ofList CD31
  exact satisfiesDedekindCriterion_of_certificate_lists T l 193 T_ofList CD193

noncomputable def M2 : MaximalOrderCertificateLists 2 O Om hm where
 m := 2
 n := 1
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 1, 0], [1, 0, 0], [0, 0, 1]], 
![[0, 0, 1], [0, 0, 1], [1, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 1, 0],![0, 0, 1]]
 b2 := ![![1, 0, 0]]
 v := ![![1, 1, 0],![0, 0, 1]]
 w := ![![1, 0, 0]]
 wFrob := ![![1, 0, 0]]
 v_ind := ![0, 2]
 w_ind := ![0]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 0, 0],![0, 0, 1],![1, 1, 0]]
 a := ![![![1, 0],![0, 1]],![![-6, 0],![19, -6]],![![4, 6],![-6, 0]]]
 c := ![![![0],![0]],![![57],![-38]],![![0],![57]]]
 d := ![![![0, 0]],![![0, 2]],![![2, 0]]]
 e := ![![![1]],![![0]],![![0]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inl 1, Sum.inl 0),(Sum.inl 1, Sum.inr 0)]
 hindab := by decide
 hmul1 := by decide
 hmul2 := by decide
            
noncomputable def M3 : MaximalOrderCertificateOfUnramifiedLists 3 O Om hm where
 n := 3
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0], [0, 1, 0], [0, 0, 1]], 
![[0, 1, 0], [0, 2, 0], [0, 0, 2]], 
![[0, 0, 1], [0, 0, 2], [0, 1, 0]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0],![0, 1, 0],![0, 0, 2]]
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

