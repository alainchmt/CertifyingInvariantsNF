
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF5_1_2025000000_8.Irreducible5_1_2025000000_8
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 15*X^3 - 10*X^2 + 210*X + 612
lemma T_def : T = X^5 - 15*X^3 - 10*X^2 + 210*X + 612 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [612, 210, -10, -15, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/282*a^4 + 9/47*a^3 + 27/94*a^2 + 67/141*a + 19/47] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d := 282
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![282, 0, 0, 0, 0], ![0, 282, 0, 0, 0], ![0, 0, 282, 0, 0], ![0, 0, 0, 282, 0], ![114, 134, 81, 54, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-114, -134, -81, -54, 282],![-24, -26, -15, -10, 54]], 
![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![-114, -134, -81, -54, 282],![-612, -210, 10, 15, 0],![-156, -88, -26, -15, 96]], 
![![0, 0, 0, 1, 0],![-114, -134, -81, -54, 282],![-612, -210, 10, 15, 0],![-1710, -2622, -1425, -800, 4230],![-594, -642, -313, -176, 954]], 
![![0, 0, 0, 0, 1],![-24, -26, -15, -10, 54],![-156, -88, -26, -15, 96],![-594, -642, -313, -176, 954],![-180, -167, -77, -44, 243]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-282]],![[], [], [], [-79524], [-15228, -282]],![[], [], [-79524], [0, -79524], [-27072, -15228, -282]],![[], [-282], [-15228, -282], [-27072, -15228, -282], [-10646, -3093, -108, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-114, -134, -81, -54, 282], [-24, -26, -15, -10, 54]], 
 ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [-114, -134, -81, -54, 282], [-612, -210, 10, 15, 0], [-156, -88, -26, -15, 96]], 
 ![[0, 0, 0, 1, 0], [-114, -134, -81, -54, 282], [-612, -210, 10, 15, 0], [-1710, -2622, -1425, -800, 4230], [-594, -642, -313, -176, 954]], 
 ![[0, 0, 0, 0, 1], [-24, -26, -15, -10, 54], [-156, -88, -26, -15, 96], [-594, -642, -313, -176, 954], [-180, -167, -77, -44, 243]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp47: Fact $ Nat.Prime 47 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [-122, -41, 4, 5, 1]
 g := [2, 1]
 h := [1, 2, 4, 3, 1]
 a := [3]
 b := [1, 1, 1, 2]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 47] where
 n := 4
 p := ![2, 3, 5, 47]
 exp := ![8, 6, 8, 2]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp47.out
 a := [248400000000, -77152500000, 29565000000, -4387500000]
 b := [42930000000, -19467000000, 10165500000, -5913000000, 877500000]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 0, 1, 0, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 1, 0, 0], [0, 1, 1, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 1, 0, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 1, 1, 1, 0],![0, 1, 1, 1, 0],![0, 0, 1, 0, 1],![0, 1, 0, 0, 1],![0, 0, 1, 1, 0]]
 w1 := ![1, 1]
 w2 := ![0, 0, 0]
 a := ![![1375, -3142],![1374, -3143],![328, -728],![344, -828],![1320, -2982]]
 c := ![![-2856, 4794, -8686],![-2856, 4794, -8686],![-1353, 1170, -2310],![-798, 1311, -2316],![-2742, 4512, -8243]]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 1, 0, 2, 0]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 2, 1, 0, 0]], 
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 2, 1, 0]], 
![[0, 0, 0, 0, 1], [0, 1, 0, 2, 0], [0, 2, 1, 0, 0], [0, 0, 2, 1, 0], [0, 1, 1, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 2, 0],![0, 0, 1, 2, 0],![0, 0, 0, 0, 1]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 0, 2, 0],![0, 0, 1, 2, 0],![0, 0, 0, 0, 1]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 0, 0, 1, 0]]
 v_ind := ![1, 2, 4]
 w_ind := ![0, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![0, 0, 1, 0, 1],![0, 1, 0, 1, 0],![2, 2, 2, 2, 4],![0, 2, 0, 4, 4],![0, 2, 2, 2, 0]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![1078, -1482, 4749],![4761, -6662, 20184],![13707, -19116, 58610],![22653, -31638, 95856],![9651, -13458, 41124]]
 c := ![![-1842, -1689],![-2994, -5733],![-11544, -17469],![-15400, -27663],![-7800, -12217]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide 

noncomputable def M47 : MaximalOrderCertificateOfUnramifiedLists 47 O Om hm where
 n := 5
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [27, 7, 13, 40, 0], [23, 21, 32, 37, 7]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [27, 7, 13, 40, 0], [46, 25, 10, 15, 0], [32, 6, 21, 32, 2]], 
![[0, 0, 0, 1, 0], [27, 7, 13, 40, 0], [46, 25, 10, 15, 0], [29, 10, 32, 46, 0], [17, 16, 16, 12, 14]], 
![[0, 0, 0, 0, 1], [23, 21, 32, 37, 7], [32, 6, 21, 32, 2], [17, 16, 16, 12, 14], [8, 21, 17, 3, 8]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![26, 45, 28, 46, 0],![41, 27, 37, 12, 0],![36, 18, 30, 12, 0],![12, 32, 33, 12, 1]]
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

