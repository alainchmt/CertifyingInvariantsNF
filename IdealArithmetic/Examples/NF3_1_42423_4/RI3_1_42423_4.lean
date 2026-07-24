
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF3_1_42423_4.Irreducible3_1_42423_4
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^3 + 21*X - 113
lemma T_def : T = X^3 + 21*X - 113 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-113, 21, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/3*a^2 - 1/3*a + 1/3] 

noncomputable def BQ : SubalgebraBuilderLists 3 ℤ  ℚ K T l where
 d := 3
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![3, 0, 0], ![0, 3, 0], ![1, -1, 1]]
 a := ![ ![![1, 0, 0],![0, 1, 0],![0, 0, 1]], 
![![0, 1, 0],![-1, 1, 3],![38, -7, -1]], 
![![0, 0, 1],![38, -7, -1],![-23, 15, -6]]]
 s := ![![[], [], []],![[], [], [-3]],![[], [-3], [2, -1]]]
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
 ![[0, 1, 0], [-1, 1, 3], [38, -7, -1]], 
 ![[0, 0, 1], [38, -7, -1], [-23, 15, -6]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0] [] (by decide)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp179: Fact $ Nat.Prime 179 := fact_iff.2 (by norm_num)
instance hp79: Fact $ Nat.Prime 79 := fact_iff.2 (by norm_num)

def CD79: CertificateDedekindCriterionLists l 79 where
 n := 2
 a' := [59]
 b' := [46, 10]
 k := [50, 1]
 f := [11, 17, 1]
 g := [14, 25, 1]
 h := [54, 1]
 a := [18, 28]
 b := [48, 51]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD179: CertificateDedekindCriterionLists l 179 where
 n := 2
 a' := [37]
 b' := [50, 71]
 k := [144, 1]
 f := [9, 43, 1]
 g := [14, 72, 1]
 h := [107, 1]
 a := [72, 56]
 b := [120, 123]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
 n := 3
 p := ![3, 79, 179]
 exp := ![3, 1, 1]
 pdgood := [79, 179]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp3.out
  exact hp79.out
  exact hp179.out
 a := [-3051, -378]
 b := [1764, 1017, 126]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 79 T_ofList CD79
  exact satisfiesDedekindCriterion_of_certificate_lists T l 179 T_ofList CD179

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
![[0, 1, 0], [2, 1, 0], [2, 2, 2]], 
![[0, 0, 1], [2, 2, 2], [1, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 1, 0]]
 b2 := ![![1, 0, 0],![0, 0, 1]]
 v := ![![1, 1, 0]]
 w := ![![1, 0, 0],![0, 0, 1]]
 wFrob := ![![1, 0, 0],![0, 0, 1]]
 v_ind := ![0]
 w_ind := ![0, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![0, 0, 2],![2, 2, 0],![1, 0, 1]]
 a := ![![![-14]],![![6]],![![-6]]]
 c := ![![![30, 0]],![![-2, 2]],![![15, 0]]]
 d := ![![![0],![90]],![![6],![-42]],![![0],![45]]]
 e := ![![![0, 2],![-76, -12]],![![0, 0],![90, 0]],![![1, 1],![-38, -5]]]
 ab_ind := ![(Sum.inl 0, Sum.inl 0),(Sum.inl 0, Sum.inr 0),(Sum.inr 0, Sum.inr 0)]
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

