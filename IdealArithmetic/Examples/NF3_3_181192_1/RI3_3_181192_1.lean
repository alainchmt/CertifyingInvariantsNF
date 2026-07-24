
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_3_181192_1.Irreducible3_3_181192_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 - X^2 - 104*X - 212
lemma T_def : T = X^3 - X^2 - 104*X - 212 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-212, -104, -1, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/4*a^2 + 1/4*a - 1/2] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 4
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![4, 0, 0], ![0, 4, 0], ![-2, 1, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![2, -1, 4],![54, 25, 2]], 
![![0, 0, 1],![54, 25, 2],![53, 26, 26]]]
 s := ![![[], [], []],![[], [], [-4]],![[], [-4], [-3, -1]]]
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
 ![[0, 1, 0], [2, -1, 4], [54, 25, 2]], 
 ![[0, 0, 1], [54, 25, 2], [53, 26, 26]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp11: Fact $ Nat.Prime 11 := fact_iff.2 (by norm_num)
instance hp29: Fact $ Nat.Prime 29 := fact_iff.2 (by norm_num)
instance hp71: Fact $ Nat.Prime 71 := fact_iff.2 (by norm_num)

def CD11: CertificateDedekindCriterionLists l 11 where
 n := 2
 a' := [8]
 b' := [4, 7]
 k := [8, 1]
 f := [20, 11, 1]
 g := [8, 9, 1]
 h := [1, 1]
 a := [4, 5]
 b := [8, 6]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD29: CertificateDedekindCriterionLists l 29 where
 n := 2
 a' := [20]
 b' := [27, 19]
 k := [25, 1]
 f := [20, 11, 1]
 g := [23, 12, 1]
 h := [16, 1]
 a := [5, 7]
 b := [2, 22]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD71: CertificateDedekindCriterionLists l 71 where
 n := 2
 a' := [17]
 b' := [36, 27]
 k := [30, 1]
 f := [12, 16, 1]
 g := [32, 50, 1]
 h := [20, 1]
 a := [37, 60]
 b := [15, 11]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2] where
 n := 4
 p := ![2, 11, 29, 71]
 exp := ![7, 1, 1, 1]
 pdgood := [11, 29, 71]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp11.out
  exact hp29.out
  exact hp71.out
 a := [7288, -1878]
 b := [-42732, -2638, 626]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 11 T_ofList CD11
  exact satisfiesDedekindCriterion_of_certificate_lists T l 29 T_ofList CD29
  exact satisfiesDedekindCriterion_of_certificate_lists T l 71 T_ofList CD71

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
![[0, 1, 0], [0, 1, 0], [0, 1, 0]], 
![[0, 0, 1], [0, 1, 0], [1, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 1]]
 b2 := ![![1, 0, 0],![0, 1, 0]]
 v := ![![1, 0, 1]]
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
 a := ![![![1]],![![30]],![![2]]]
 c := ![![![0, 0]],![![39, 26]],![![26, 13]]]
 d := ![![![0],![0]],![![2],![12]],![![0],![8]]]
 e := ![![![1, 0],![0, 1]],![![0, 1],![50, 25]],![![0, 1],![-2, -1]]]
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

