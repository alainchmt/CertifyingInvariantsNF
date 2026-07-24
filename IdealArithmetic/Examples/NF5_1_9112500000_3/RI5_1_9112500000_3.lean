
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF5_1_9112500000_3.Irreducible5_1_9112500000_3
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^5 + 75*X^3 - 50*X^2 + 1500*X - 1800
lemma T_def : T = X^5 + 75*X^3 - 50*X^2 + 1500*X - 1800 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-1800, 1500, -50, 75, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, a^2, 1/10*a^3 - 1/2*a, 1/120*a^4 - 1/20*a^3 + 1/8*a^2 - 1/6*a - 1/2] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d := 120
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![120, 0, 0, 0, 0], ![0, 120, 0, 0, 0], ![0, 0, 120, 0, 0], ![0, -60, 0, 12, 0], ![-60, -20, 15, -6, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 5, 0, 10, 0],![6, 5, -2, 6, 12],![12, -18, 1, -8, -6]], 
![![0, 0, 1, 0, 0],![0, 5, 0, 10, 0],![60, 50, -15, 60, 120],![180, -190, 5, -80, 0],![-120, 85, -8, 10, -60]], 
![![0, 0, 0, 1, 0],![6, 5, -2, 6, 12],![180, -190, 5, -80, 0],![-51, -22, -2, -46, -102],![-72, 106, 0, 50, 51]], 
![![0, 0, 0, 0, 1],![12, -18, 1, -8, -6],![-120, 85, -8, 10, -60],![-72, 106, 0, 50, 51],![87, -93, 3, -29, -9]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-120]],![[], [], [], [-1440], [720, -120]],![[], [], [-1440], [0, -144], [780, 72, -12]],![[], [-120], [720, -120], [780, 72, -12], [-730, 9, 12, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 5, 0, 10, 0], [6, 5, -2, 6, 12], [12, -18, 1, -8, -6]], 
 ![[0, 0, 1, 0, 0], [0, 5, 0, 10, 0], [60, 50, -15, 60, 120], [180, -190, 5, -80, 0], [-120, 85, -8, 10, -60]], 
 ![[0, 0, 0, 1, 0], [6, 5, -2, 6, 12], [180, -190, 5, -80, 0], [-51, -22, -2, -46, -102], [-72, 106, 0, 50, 51]], 
 ![[0, 0, 0, 0, 1], [12, -18, 1, -8, -6], [-120, 85, -8, 10, -60], [-72, 106, 0, 50, 51], [87, -93, 3, -29, -9]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 5] where
 n := 3
 p := ![2, 3, 5]
 exp := ![13, 8, 12]
 pdgood := []
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
 a := [-1215000000000, -911250000000, 0, 60750000000]
 b := [7290000000000, 607500000000, -182250000000, 0, -12150000000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp

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
![[0, 0, 0, 1, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 0, 0, 0], [0, 0, 0, 0, 1]], 
![[0, 0, 0, 0, 1], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 0, 0, 1], [1, 1, 1, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![1, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 0, 1, 0],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![1, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 1],![0, 0, 1, 0, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 0, 1, 0, 0],![0, 1, 1, 0, 1],![0, 0, 1, 0, 1],![1, 1, 1, 1, 0],![0, 1, 1, 0, 0]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![11, -6],![62, -11],![46, -12],![-78, -8],![26, -6]]
 c := ![![56, 60, -118],![-40, 54, -36],![-29, 48, -36],![204, 33, -182],![44, 66, -119]]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 2, 0, 1, 0], [0, 2, 1, 0, 0], [0, 0, 1, 1, 0]], 
![[0, 0, 1, 0, 0], [0, 2, 0, 1, 0], [0, 2, 0, 0, 0], [0, 2, 2, 1, 0], [0, 1, 1, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 2, 1, 0, 0], [0, 2, 2, 1, 0], [0, 2, 1, 2, 0], [0, 1, 0, 2, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 1, 1, 0], [0, 1, 1, 1, 0], [0, 1, 0, 2, 0], [0, 0, 0, 1, 0]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 0, 1],![0, 0, 1, 0, 2],![0, 0, 0, 1, 2]]
 b2 := ![![1, 0, 0, 0, 0],![0, 2, 0, 0, 0]]
 v := ![![0, 1, 0, 0, 1],![0, 0, 1, 0, 2],![0, 0, 0, 1, 2]]
 w := ![![1, 0, 0, 0, 0],![0, 2, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 2, 0]]
 v_ind := ![1, 2, 3]
 w_ind := ![0, 1]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![2, 0, 1, 0, 0],![1, 2, 2, 0, 1],![1, 1, 1, 2, 2],![0, 2, 0, 0, 2],![0, 0, 2, 1, 0]]
 w1 := ![1, 1, 1]
 w2 := ![0, 1]
 a := ![![-278, -48, 102],![-381, -65, 12],![-99, -33, 127],![336, 48, -330],![-633, -111, 366]]
 c := ![![-120, 102],![-87, 78],![-6, 42],![262, -216],![-303, 271]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inr 0, Sum.inr 1]
 hacindw := by decide 

noncomputable def M5 : MaximalOrderCertificateWLists 5 O Om hm where
 m := 4
 n := 1
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [1, 0, 3, 1, 2], [2, 2, 1, 2, 4]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 0, 0, 0], [0, 0, 2, 0, 0]], 
![[0, 0, 0, 1, 0], [1, 0, 3, 1, 2], [0, 0, 0, 0, 0], [4, 3, 3, 4, 3], [3, 1, 0, 0, 1]], 
![[0, 0, 0, 0, 1], [2, 2, 1, 2, 4], [0, 0, 2, 0, 0], [3, 1, 0, 0, 1], [2, 2, 3, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 0, 2],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0]]
 v := ![![1, 0, 0, 0, 2],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0]]
 v_ind := ![0, 1, 2, 3]
 w_ind := ![0]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![4, 4, 4, 0, 1],![4, 1, 2, 2, 3],![3, 0, 0, 3, 1],![0, 0, 0, 4, 2],![0, 0, 4, 0, 0]]
 w1 := ![1, 1, 1, 0]
 w2 := ![1]
 a := ![![-59, 685, -85, 280],![-5, 126, -40, 70],![135, -35, 11, 40],![150, -130, 10, 16],![0, 900, -100, 360]]
 c := ![![-95],![-5],![15],![30],![-144]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inl 2, Sum.inl 3, Sum.inr 0]
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

