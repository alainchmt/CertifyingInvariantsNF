
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF5_1_632812500_6.Irreducible5_1_632812500_6
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^5 - 25*X^3 - 50*X^2 + 300*X + 470
lemma T_def : T = X^5 - 25*X^3 - 50*X^2 + 300*X + 470 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [470, 300, -50, -25, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis [1, a, a^2, a^3, 1/438*a^4 - 61/438*a^3 + 32/73*a^2 + 32/219*a - 50/219] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d := 438
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![438, 0, 0, 0, 0], ![0, 438, 0, 0, 0], ![0, 0, 438, 0, 0], ![0, 0, 0, 438, 0], ![-100, 64, 192, -61, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![100, -64, -192, 61, 438],![-15, 8, 27, -8, -61]], 
![![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![100, -64, -192, 61, 438],![-470, -300, 50, 25, 0],![115, 9, -103, 27, 217]], 
![![0, 0, 0, 1, 0],![100, -64, -192, 61, 438],![-470, -300, 50, 25, 0],![2500, -2070, -5100, 1575, 10950],![-555, 123, 684, -192, -1411]], 
![![0, 0, 0, 0, 1],![-15, 8, 27, -8, -61],![115, 9, -103, 27, 217],![-555, 123, 684, -192, -1411],![130, -11, -139, 38, 287]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-438]],![[], [], [], [-191844], [26718, -438]],![[], [], [-191844], [0, -191844], [-95046, 26718, -438]],![[], [-438], [26718, -438], [-95046, 26718, -438], [26296, -4130, 122, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [100, -64, -192, 61, 438], [-15, 8, 27, -8, -61]], 
 ![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [100, -64, -192, 61, 438], [-470, -300, 50, 25, 0], [115, 9, -103, 27, 217]], 
 ![[0, 0, 0, 1, 0], [100, -64, -192, 61, 438], [-470, -300, 50, 25, 0], [2500, -2070, -5100, 1575, 10950], [-555, 123, 684, -192, -1411]], 
 ![[0, 0, 0, 0, 1], [-15, 8, 27, -8, -61], [115, 9, -103, 27, 217], [-555, 123, 684, -192, -1411], [130, -11, -139, 38, 287]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)
instance hp73: Fact $ Nat.Prime 73 := fact_iff.2 (by norm_num)
instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n := 5
 a' := []
 b' := [1]
 k := [1]
 f := [-94, -60, 10, 5]
 g := [0, 1]
 h := [0, 0, 0, 0, 1]
 a := [1]
 b := []
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [73, 2, 3] where
 n := 4
 p := ![2, 3, 5, 73]
 exp := ![4, 6, 9, 2]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp73.out
 a := [-44803125000, 117450000000, 22528125000, -5821875000]
 b := [474862500000, 19085625000, -35133750000, -4505625000, 1164375000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M73 : MaximalOrderCertificateOfUnramifiedLists 73 O Om hm where
 n := 5
 t := 1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [27, 9, 27, 61, 0], [58, 8, 27, 65, 12]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [27, 9, 27, 61, 0], [41, 65, 50, 25, 0], [42, 9, 43, 27, 71]], 
![[0, 0, 0, 1, 0], [27, 9, 27, 61, 0], [41, 65, 50, 25, 0], [18, 47, 10, 42, 0], [29, 50, 27, 27, 49]], 
![[0, 0, 0, 0, 1], [58, 8, 27, 65, 12], [42, 9, 43, 27, 71], [29, 50, 27, 27, 49], [57, 62, 7, 38, 68]]]
 hTMod := by decide
 hle := by decide
 w := ![![1, 0, 0, 0, 0],![16, 62, 63, 32, 0],![11, 10, 58, 22, 0],![13, 45, 1, 27, 0],![49, 18, 15, 25, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]]
 w_ind := ![0, 1, 2, 3, 4]
 hindw := by decide
 hwFrobComp := by decide 
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [1, 0, 1, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [1, 1, 1, 1, 1]], 
![[0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [0, 0, 0, 1, 0], [1, 1, 0, 0, 1]], 
![[0, 0, 0, 0, 1], [1, 0, 1, 0, 1], [1, 1, 1, 1, 1], [1, 1, 0, 0, 1], [0, 1, 1, 0, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![0, 1, 0, 1, 0],![0, 0, 1, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 1],![0, 0, 0, 1, 0]]
 v_ind := ![1, 2]
 w_ind := ![0, 1, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 1, 1, 0, 0],![1, 0, 0, 0, 1],![0, 0, 1, 0, 0],![1, 1, 1, 0, 1],![0, 0, 0, 1, 0]]
 w1 := ![1, 1]
 w2 := ![0, 1, 0]
 a := ![![901, -624],![-1372, 1069],![466, -298],![-472, 444],![12332, -9358]]
 c := ![![-220, 814, -1642],![-390, -1106, 1922],![-305, 436, -992],![-610, -293, 280],![1860, 10196, -18555]]
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
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [1, 2, 0, 1, 0], [0, 2, 0, 1, 2]], 
![[0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [1, 2, 0, 1, 0], [1, 0, 2, 1, 0], [1, 0, 2, 0, 1]], 
![[0, 0, 0, 1, 0], [1, 2, 0, 1, 0], [1, 0, 2, 1, 0], [1, 0, 0, 0, 0], [0, 0, 0, 0, 2]], 
![[0, 0, 0, 0, 1], [0, 2, 0, 1, 2], [1, 0, 2, 0, 1], [0, 0, 0, 0, 2], [1, 1, 2, 2, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 2, 0, 0],![0, 1, 0, 2, 0]]
 b2 := ![![1, 0, 0, 0, 0],![2, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 2, 0, 0],![0, 1, 0, 2, 0]]
 w := ![![1, 0, 0, 0, 0],![2, 1, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 2, 0, 1],![0, 0, 0, 1, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 3]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![2, 0, 4, 0, 2],![0, 0, 0, 0, 2],![2, 2, 4, 0, 4],![0, 4, 2, 0, 4],![0, 4, 2, 2, 2]]
 w1 := ![0, 1]
 w2 := ![1, 1, 0]
 a := ![![659, -30],![1059, -302],![1419, -234],![1320, -273],![-8655, 2856]]
 c := ![![-339, -594, 6],![2055, -1464, 1728],![995, -1596, 1176],![1470, -1570, 1479],![-21015, 12840, -16822]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
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

