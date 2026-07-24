
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF5_3_125000000_3.Irreducible5_3_125000000_3
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 25*X^3 - 50*X^2 + 160
lemma T_def : T = X^5 - 25*X^3 - 50*X^2 + 160 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [160, 0, -50, -25, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/152*a^4 - 2/19*a^3 - 73/152*a^2 + 27/76*a + 6/19] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d := 152
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![152, 0, 0, 0, 0], ![0, 152, 0, 0, 0], ![0, 0, 152, 0, 0], ![0, -76, 0, 76, 0], ![48, 54, -73, -16, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![-24, -19, 36, 16, 76],![4, 4, -7, -4, -16]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![-48, -38, 73, 32, 152],![-80, 12, 25, 24, 0],![32, 9, -28, -14, -48]], 
![![0, 0, 0, 1, 0],![-24, -19, 36, 16, 76],![-80, 12, 25, 24, 0],![-276, -246, 420, 209, 874],![70, 37, -76, -42, -140]], 
![![0, 0, 0, 0, 1],![4, 4, -7, -4, -16],![32, 9, -28, -14, -48],![70, 37, -76, -42, -140],![-23, -8, 21, 11, 36]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-152]],![[], [], [], [-11552], [2432, -152]],![[], [], [-11552], [0, -5776], [3724, 1216, -76]],![[], [-152], [2432, -152], [3724, 1216, -76], [-1694, -135, 32, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [-24, -19, 36, 16, 76], [4, 4, -7, -4, -16]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [-48, -38, 73, 32, 152], [-80, 12, 25, 24, 0], [32, 9, -28, -14, -48]], 
 ![[0, 0, 0, 1, 0], [-24, -19, 36, 16, 76], [-80, 12, 25, 24, 0], [-276, -246, 420, 209, 874], [70, 37, -76, -42, -140]], 
 ![[0, 0, 0, 0, 1], [4, 4, -7, -4, -16], [32, 9, -28, -14, -48], [70, 37, -76, -42, -140], [-23, -8, 21, 11, 36]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp19: Fact $ Nat.Prime 19 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [-32, 0, 10, 5]
 g := [0, 1]
 h := [0, 0, 0, 0, 1]
 a := [2]
 b := []
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 19] where
 n := 3
 p := ![2, 5, 19]
 exp := ![14, 9, 2]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp5.out
  exact hp19.out
 a := [72200000000, -22125000000, -3900000000, 1075000000]
 b := [-35400000000, -15790000000, 6575000000, 780000000, -215000000]
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
 g := ![![0, 0, 0, 0, 1],![0, 0, 0, 1, 0],![1, 0, 0, 0, 1],![0, 1, 1, 0, 0],![0, 1, 0, 1, 0]]
 w1 := ![1, 0]
 w2 := ![1, 0, 0]
 a := ![![-149, 66],![734, -365],![-148, 66],![164, -62],![794, -396]]
 c := ![![114, -14, 52],![-510, 84, -270],![115, -14, 52],![-140, 17, -54],![-550, 94, -293]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M19 : MaximalOrderCertificateOfUnramifiedLists 19 O Om hm where
 n := 5
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [14, 0, 17, 16, 0], [4, 4, 12, 15, 3]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [9, 0, 16, 13, 0], [15, 12, 6, 5, 0], [13, 9, 10, 5, 9]], 
![[0, 0, 0, 1, 0], [14, 0, 17, 16, 0], [15, 12, 6, 5, 0], [9, 1, 2, 0, 0], [13, 18, 0, 15, 12]], 
![[0, 0, 0, 0, 1], [4, 4, 12, 15, 3], [13, 9, 10, 5, 9], [13, 18, 0, 15, 12], [15, 11, 2, 11, 17]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![11, 18, 0, 17, 0],![4, 1, 1, 1, 0],![0, 0, 0, 1, 0],![1, 5, 0, 5, 1]]
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

