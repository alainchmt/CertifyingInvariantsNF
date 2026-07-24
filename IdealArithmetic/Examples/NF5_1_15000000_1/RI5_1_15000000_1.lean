
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF5_1_15000000_1.Irreducible5_1_15000000_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 10*X^3 - 20*X^2 + 45*X + 108
lemma T_def : T = X^5 - 10*X^3 - 20*X^2 + 45*X + 108 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [108, 45, -20, -10, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, a^2, 1/4*a^3 - 1/2*a^2 - 1/4*a, 1/12*a^4 - 1/12*a^2 - 1/6*a] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d := 12
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![12, 0, 0, 0, 0], ![0, 12, 0, 0, 0], ![0, 0, 12, 0, 0], ![0, -3, -6, 3, 0], ![0, -2, -1, 0, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 2, 4, 0],![0, 0, -1, -2, 3],![-9, -3, 3, 3, 0]], 
![![0, 0, 1, 0, 0],![0, 1, 2, 4, 0],![0, 2, 1, 0, 12],![-27, -10, 9, 9, -6],![0, -6, 0, 6, 9]], 
![![0, 0, 0, 1, 0],![0, 0, -1, -2, 3],![-27, -10, 9, 9, -6],![27, 5, -9, -4, 9],![-18, -3, 3, 0, 0]], 
![![0, 0, 0, 0, 1],![-9, -3, 3, 3, 0],![0, -6, 0, 6, 9],![-18, -3, 3, 0, 0],![-12, -9, 3, 6, 3]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-12]],![[], [], [], [-36], [0, -12]],![[], [], [-36], [36, -9], [-24, 6, -3]],![[], [-12], [0, -12], [-24, 6, -3], [-16, -8, 0, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 2, 4, 0], [0, 0, -1, -2, 3], [-9, -3, 3, 3, 0]], 
 ![[0, 0, 1, 0, 0], [0, 1, 2, 4, 0], [0, 2, 1, 0, 12], [-27, -10, 9, 9, -6], [0, -6, 0, 6, 9]], 
 ![[0, 0, 0, 1, 0], [0, 0, -1, -2, 3], [-27, -10, 9, 9, -6], [27, 5, -9, -4, 9], [-18, -3, 3, 0, 0]], 
 ![[0, 0, 0, 0, 1], [-9, -3, 3, 3, 0], [0, -6, 0, 6, 9], [-18, -3, 3, 0, 0], [-12, -9, 3, 6, 3]]]

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
 f := [-21, -7, 7, 4, 1]
 g := [3, 1]
 h := [1, 3, 4, 2, 1]
 a := [1]
 b := [4, 1, 4, 4]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3] where
 n := 3
 p := ![2, 3, 5]
 exp := ![14, 3, 7]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [128000000, 96000000, 144000000, -16000000]
 b := [460800000, 51200000, -32000000, -28800000, 3200000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 1], [1, 1, 1, 1, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 1], [1, 0, 1, 1, 0], [1, 1, 1, 0, 1], [0, 1, 1, 0, 0]], 
![[0, 0, 0, 0, 1], [1, 1, 1, 1, 0], [0, 0, 0, 0, 1], [0, 1, 1, 0, 0], [0, 1, 1, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 1, 1],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![1, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 0, 1, 1],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![1, 1, 0, 1, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 1, 1, 0, 1],![1, 1, 0, 1, 1],![1, 1, 0, 0, 0],![1, 0, 0, 1, 1],![0, 1, 1, 0, 0]]
 w1 := ![0, 1]
 w2 := ![1, 1, 0]
 a := ![![19, 48],![40, 7],![6, 4],![34, 4],![6, 32]]
 c := ![![-80, 14, -52],![-24, -12, 2],![1, -2, 4],![-24, -9, -2],![-42, 12, -33]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 1
 n := 4
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 2, 1, 0], [0, 0, 2, 1, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 2, 1, 0], [0, 2, 1, 0, 0], [0, 2, 0, 0, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 2, 1, 0], [0, 2, 0, 0, 0], [0, 2, 0, 2, 0], [0, 0, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 2, 1, 0],![0, 1, 2, 2, 0],![0, 1, 1, 0, 0]]
 v := ![![0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 2, 1, 0],![0, 1, 2, 2, 0],![0, 1, 1, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 v_ind := ![4]
 w_ind := ![0, 1, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 2, 2, 0, 1],![0, 1, 2, 2, 2],![0, 1, 1, 2, 0],![0, 0, 0, 1, 0],![0, 2, 1, 2, 0]]
 w1 := ![1]
 w2 := ![1, 1, 0, 1]
 a := ![![304],![363],![90],![-9],![99]]
 c := ![![-99, 99, -6, -123],![-257, 285, -72, -330],![-150, 154, -42, -165],![-60, 66, -23, -69],![-153, 153, -36, -167]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3]
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

