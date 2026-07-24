
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF5_3_15187500000_5.Irreducible5_3_15187500000_5
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 25*X^3 - 350*X^2 + 1200*X + 320
lemma T_def : T = X^5 - 25*X^3 - 350*X^2 + 1200*X + 320 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [320, 1200, -350, -25, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, a^2, 1/26*a^3 - 2/13*a^2 - 1/26*a + 6/13, 1/312*a^4 - 1/78*a^3 - 35/104*a^2 + 71/156*a + 1/3] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d := 312
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![312, 0, 0, 0, 0], ![0, 312, 0, 0, 0], ![0, 0, 312, 0, 0], ![144, -12, -48, 12, 0], ![104, 142, -105, -4, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![-12, 1, 4, 26, 0],![-4, -5, 4, 0, 12],![4, -2, -1, -8, -4]], 
![![0, 0, 1, 0, 0],![-12, 1, 4, 26, 0],![-152, -138, 121, 104, 312],![0, -24, -1, 8, -48],![28, 51, -34, 6, -80]], 
![![0, 0, 0, 1, 0],![-4, -5, 4, 0, 12],![0, -24, -1, 8, -48],![-8, 6, 2, 13, 18],![-2, -3, 6, -10, 28]], 
![![0, 0, 0, 0, 1],![4, -2, -1, -8, -4],![28, 51, -34, 6, -80],![-2, -3, 6, -10, 28],![-1, -18, 7, -11, 6]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-312]],![[], [], [], [-3744], [1248, -312]],![[], [], [-3744], [1152, -144], [780, 96, -12]],![[], [-312], [1248, -312], [780, 96, -12], [-1274, 169, 8, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [-12, 1, 4, 26, 0], [-4, -5, 4, 0, 12], [4, -2, -1, -8, -4]], 
 ![[0, 0, 1, 0, 0], [-12, 1, 4, 26, 0], [-152, -138, 121, 104, 312], [0, -24, -1, 8, -48], [28, 51, -34, 6, -80]], 
 ![[0, 0, 0, 1, 0], [-4, -5, 4, 0, 12], [0, -24, -1, 8, -48], [-8, 6, 2, 13, 18], [-2, -3, 6, -10, 28]], 
 ![[0, 0, 0, 0, 1], [4, -2, -1, -8, -4], [28, 51, -34, 6, -80], [-2, -3, 6, -10, 28], [-1, -18, 7, -11, 6]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)
instance hp13: Fact $ Nat.Prime 13 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [-64, -240, 70, 5]
 g := [0, 1]
 h := [0, 0, 0, 0, 1]
 a := [1]
 b := []
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 13] where
 n := 4
 p := ![2, 3, 5, 13]
 exp := ![13, 7, 9, 4]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp13.out
 a := [772059600000000, 43462575000000, -9582300000000, -5817825000000]
 b := [626956200000000, -417925170000000, -20328165000000, 1916460000000, 1163565000000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 1, 0, 0, 0], [1, 0, 1, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 1, 1, 1],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 v := ![![1, 0, 1, 1, 1],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 0, 1, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 2, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![0, 0, 0, 0, 1],![0, 1, 1, 1, 0],![1, 0, 0, 0, 1],![0, 1, 1, 0, 0],![0, 1, 0, 1, 0]]
 w1 := ![1, 0]
 w2 := ![1, 0, 0]
 a := ![![-43, 22],![190, -87],![-42, 22],![192, -96],![6, 8]]
 c := ![![34, 4, 14],![-168, -24, -20],![35, 4, 14],![-164, -9, -28],![-14, -16, 13]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 2
 n := 3
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 1, 2, 0], [2, 1, 1, 0, 0], [1, 1, 2, 1, 2]], 
![[0, 0, 1, 0, 0], [0, 1, 1, 2, 0], [1, 0, 1, 2, 0], [0, 0, 2, 2, 0], [1, 0, 2, 0, 1]], 
![[0, 0, 0, 1, 0], [2, 1, 1, 0, 0], [0, 0, 2, 2, 0], [1, 0, 2, 1, 0], [1, 0, 0, 2, 1]], 
![[0, 0, 0, 0, 1], [1, 1, 2, 1, 2], [1, 0, 2, 0, 1], [1, 0, 0, 2, 1], [2, 0, 1, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 2, 0],![0, 0, 1, 2, 0]]
 b2 := ![![1, 0, 0, 0, 0],![1, 1, 0, 0, 1],![2, 0, 0, 0, 2]]
 v := ![![1, 0, 0, 2, 0],![0, 0, 1, 2, 0]]
 w := ![![1, 0, 0, 0, 0],![1, 1, 0, 0, 1],![2, 0, 0, 0, 2]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 1],![0, 0, 1, 1, 2]]
 v_ind := ![0, 2]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 1, 2, 0, 1],![2, 1, 1, 0, 0],![0, 2, 1, 0, 2],![0, 1, 1, 2, 2],![2, 2, 0, 2, 2]]
 w1 := ![1, 0]
 w2 := ![1, 0, 0]
 a := ![![-17, 24],![0, 10],![-54, 42],![-24, 42],![-36, 48]]
 c := ![![39, -36, 0],![24, -18, -3],![-14, -24, 24],![-48, -14, 27],![-84, 0, 40]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M13 : MaximalOrderCertificateOfUnramifiedLists 13 O Om hm where
 n := 5
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 1, 4, 0, 0], [9, 8, 4, 0, 12], [4, 11, 12, 5, 9]], 
![[0, 0, 1, 0, 0], [1, 1, 4, 0, 0], [4, 5, 4, 0, 0], [0, 2, 12, 8, 4], [2, 12, 5, 6, 11]], 
![[0, 0, 0, 1, 0], [9, 8, 4, 0, 12], [0, 2, 12, 8, 4], [5, 6, 2, 0, 5], [11, 10, 6, 3, 2]], 
![[0, 0, 0, 0, 1], [4, 11, 12, 5, 9], [2, 12, 5, 6, 11], [11, 10, 6, 3, 2], [12, 8, 7, 2, 6]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide 

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

