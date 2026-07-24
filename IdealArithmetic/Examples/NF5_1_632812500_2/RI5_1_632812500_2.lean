
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF5_1_632812500_2.Irreducible5_1_632812500_2
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 50*X^2 - 225*X - 270
lemma T_def : T = X^5 - 50*X^2 - 225*X - 270 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-270, -225, -50, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, 1/2*a^2 - 1/2*a, 1/4*a^3 + 1/4*a - 1/2, 1/24*a^4 - 1/8*a^3 - 1/8*a^2 + 7/24*a + 1/4] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d := 24
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![24, 0, 0, 0, 0], ![0, 24, 0, 0, 0], ![0, -12, 12, 0, 0], ![-12, 6, 0, 6, 0], ![6, 7, -3, -3, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 1, 2, 0, 0],![1, -1, -1, 2, 0],![0, -2, 2, 3, 6],![11, 13, 4, -2, -3]], 
![![0, 0, 1, 0, 0],![1, -1, -1, 2, 0],![-1, -1, 2, 1, 6],![34, 35, 11, -1, -3],![-20, -14, 1, 5, 0]], 
![![0, 0, 0, 1, 0],![0, -2, 2, 3, 6],![34, 35, 11, -1, -3],![6, 27, 29, 13, 3],![-4, -23, -7, 10, 13]], 
![![0, 0, 0, 0, 1],![11, 13, 4, -2, -3],![-20, -14, 1, 5, 0],![-4, -23, -7, 10, 13],![35, 42, 10, -9, -4]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-24]],![[], [], [], [-72], [48, -12]],![[], [], [-72], [0, -36], [12, 18, -6]],![[], [-24], [48, -12], [12, 18, -6], [-82, -3, 6, -1]]]
 h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide 

lemma T_degree : T.natDegree = 5 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin 5) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 5) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ

noncomputable def B : Basis (Fin 5) ℤ O := timesTableO.basis
def Table : Fin 5 → Fin 5 → List ℤ := 
 ![ ![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
 ![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [1, -1, -1, 2, 0], [0, -2, 2, 3, 6], [11, 13, 4, -2, -3]], 
 ![[0, 0, 1, 0, 0], [1, -1, -1, 2, 0], [-1, -1, 2, 1, 6], [34, 35, 11, -1, -3], [-20, -14, 1, 5, 0]], 
 ![[0, 0, 0, 1, 0], [0, -2, 2, 3, 6], [34, 35, 11, -1, -3], [6, 27, 29, 13, 3], [-4, -23, -7, 10, 13]], 
 ![[0, 0, 0, 0, 1], [11, 13, 4, -2, -3], [-20, -14, 1, 5, 0], [-4, -23, -7, 10, 13], [35, 42, 10, -9, -4]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [54, 45, 10]
 g := [0, 1]
 h := [0, 0, 0, 0, 1]
 a := [4]
 b := []
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![14, 6, 9]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-288900000000, 48600000000, -24300000000, 10800000000]
 b := [243000000000, 122580000000, -9720000000, 4860000000, -2160000000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 2
 n := 3
 t := 3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [1, 1, 1, 0, 0], [0, 0, 0, 1, 0], [1, 1, 0, 0, 1]], 
![[0, 0, 1, 0, 0], [1, 1, 1, 0, 0], [1, 1, 0, 1, 0], [0, 1, 1, 1, 1], [0, 0, 1, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 1, 1, 1, 1], [0, 1, 1, 1, 1], [0, 1, 1, 0, 1]], 
![[0, 0, 0, 0, 1], [1, 1, 0, 0, 1], [0, 0, 1, 1, 0], [0, 1, 1, 0, 1], [1, 0, 0, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 1, 1],![0, 1, 1, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 0, 1, 0, 0]]
 v := ![![1, 0, 0, 1, 1],![0, 1, 1, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![1, 0, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 1, 1]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 1, 1, 1, 1],![1, 0, 0, 0, 1],![1, 1, 0, 1, 0],![0, 0, 0, 1, 0],![0, 1, 1, 0, 1]]
 w1 := ![1, 0]
 w2 := ![0, 1, 1]
 a := ![![53, -12],![8, -1],![36, -10],![30, -8],![22, -4]]
 c := ![![-20, 66, 50],![-4, 10, 8],![-9, 48, 34],![-8, 39, 28],![-12, 26, 21]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 3
 n := 2
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 1, 2, 0, 0], [1, 2, 2, 2, 0], [0, 1, 2, 0, 0], [2, 1, 1, 1, 0]], 
![[0, 0, 1, 0, 0], [1, 2, 2, 2, 0], [2, 2, 2, 1, 0], [1, 2, 2, 2, 0], [1, 1, 1, 2, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 2, 0, 0], [1, 2, 2, 2, 0], [0, 0, 2, 1, 0], [2, 1, 2, 1, 1]], 
![[0, 0, 0, 0, 1], [2, 1, 1, 1, 0], [1, 1, 1, 2, 0], [2, 1, 2, 1, 1], [2, 0, 1, 0, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 1, 0, 2],![0, 1, 1, 0, 0],![0, 0, 0, 1, 2]]
 b2 := ![![1, 0, 0, 0, 0],![2, 2, 0, 0, 0]]
 v := ![![1, 0, 1, 0, 2],![0, 1, 1, 0, 0],![0, 0, 0, 1, 2]]
 w := ![![1, 0, 0, 0, 0],![2, 2, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 2, 0]]
 v_ind := ![0, 1, 3]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![2, 2, 0, 0, 0],![2, 0, 0, 4, 0],![2, 4, 2, 0, 2],![2, 4, 0, 2, 2],![0, 8, 8, 4, 8]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![-2, 66, 0],![-132, 284, 318],![-24, 312, 8],![-30, 354, 96],![-222, 1266, 348]]
 c := ![![12, 12],![228, -51],![60, 51],![128, 51],![420, 103]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide 


open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0, 0, 0, 0] = 1 := by
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

