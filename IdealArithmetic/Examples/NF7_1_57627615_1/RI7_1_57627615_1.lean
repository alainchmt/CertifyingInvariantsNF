
import IdealArithmetic.DedekindProject.CertifyRingOfIntegers
import Mathlib.Tactic.NormNum.Prime
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF7_1_57627615_1.Irreducible7_1_57627615_1
import IdealArithmetic.DedekindProject.Discriminant



open Polynomial Module

noncomputable def T : ℤ[X] := X^7 - X^6 - 5*X^4 - 5*X^2 + 2*X - 1
lemma T_def : T = X^7 - X^6 - 5*X^4 - 5*X^2 + 2*X - 1 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  exact AdjoinRoot.instAlgebra _

local notation "l" => [-1, 2, -5, 0, -5, 0, -1, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _

local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring
-- We build the subalgebra with integral basis (1, a, a^2, a^3, a^4, a^5, 1/3*a^6 + 1/3*a^3 + 1/3*a^2 - 1/3*a + 1/3) 

noncomputable def BQ : SubalgebraBuilderLists 7 ℤ  ℚ K T l where
 d := 3
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![3, 0, 0, 0, 0, 0, 0], ![0, 3, 0, 0, 0, 0, 0], ![0, 0, 3, 0, 0, 0, 0], ![0, 0, 0, 3, 0, 0, 0], ![0, 0, 0, 0, 3, 0, 0], ![0, 0, 0, 0, 0, 3, 0], ![1, -1, 1, 1, 0, 0, 1]]
 a := ![ ![![1, 0, 0, 0, 0, 0, 0],![0, 1, 0, 0, 0, 0, 0],![0, 0, 1, 0, 0, 0, 0],![0, 0, 0, 1, 0, 0, 0],![0, 0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 0, 1, 0],![0, 0, 0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0, 0, 0],![0, 0, 1, 0, 0, 0, 0],![0, 0, 0, 1, 0, 0, 0],![0, 0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 0, 1, 0],![-1, 1, -1, -1, 0, 0, 3],![0, 0, 1, 0, 2, 0, 1]], 
![![0, 0, 1, 0, 0, 0, 0],![0, 0, 0, 1, 0, 0, 0],![0, 0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 0, 1, 0],![-1, 1, -1, -1, 0, 0, 3],![0, -1, 4, -1, 5, 0, 3],![0, 0, 1, 1, 2, 2, 1]], 
![![0, 0, 0, 1, 0, 0, 0],![0, 0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 0, 1, 0],![-1, 1, -1, -1, 0, 0, 3],![0, -1, 4, -1, 5, 0, 3],![0, 0, 2, 4, 5, 5, 3],![-2, 2, -1, -1, 3, 2, 7]], 
![![0, 0, 0, 0, 1, 0, 0],![0, 0, 0, 0, 0, 1, 0],![-1, 1, -1, -1, 0, 0, 3],![0, -1, 4, -1, 5, 0, 3],![0, 0, 2, 4, 5, 5, 3],![-5, 5, -2, -3, 10, 5, 18],![-2, 0, 7, -3, 13, 3, 13]], 
![![0, 0, 0, 0, 0, 1, 0],![-1, 1, -1, -1, 0, 0, 3],![0, -1, 4, -1, 5, 0, 3],![0, 0, 2, 4, 5, 5, 3],![-5, 5, -2, -3, 10, 5, 18],![-5, 0, 18, -7, 33, 10, 33],![-3, 1, 10, 4, 23, 13, 22]], 
![![0, 0, 0, 0, 0, 0, 1],![0, 0, 1, 0, 2, 0, 1],![0, 0, 1, 1, 2, 2, 1],![-2, 2, -1, -1, 3, 2, 7],![-2, 0, 7, -3, 13, 3, 13],![-3, 1, 10, 4, 23, 13, 22],![-5, 4, 3, -1, 17, 9, 23]]]
 s := ![![[], [], [], [], [], [], []],![[], [], [], [], [], [], [-3]],![[], [], [], [], [], [-9], [-3, -3]],![[], [], [], [], [-9], [-9, -9], [-3, -3, -3]],![[], [], [], [-9], [-9, -9], [-9, -9, -9], [-21, -3, -3, -3]],![[], [], [-9], [-9, -9], [-9, -9, -9], [-54, -9, -9, -9], [-39, -21, -3, -3, -3]],![[], [-3], [-3, -3], [-3, -3, -3], [-21, -3, -3, -3], [-39, -21, -3, -3, -3], [-23, -15, -8, -1, -1, -1]]]
 h := Adj
 honed := by decide
 hd := by norm_num
 hcc := by decide
 hin := by decide
 hsymma := by decide
 hc_le := by decide 

lemma T_degree : T.natDegree = 7 := (SubalgebraBuilderOfList T l BQ).hdeg

lemma T_monic : Monic T := by
  rw [← T_ofList]
  refine monic_ofList l rfl

lemma T_irreducible : Irreducible T := irreducible_T

noncomputable def Om : Subalgebra ℤ K := integralClosure ℤ K

noncomputable def O := subalgebraOfBuilderLists T l BQ

def hm : O ≤ Om := le_integralClosure_of_basis O (basisOfBuilderLists T l BQ)

noncomputable def B' : Basis (Fin 7) ℤ Om :=
  Basis.reindex (AdjoinRoot.basisIntegralClosure T_monic
    (Irreducible.prime T_irreducible)) (finCongr T_degree)

instance OmFree : Module.Free ℤ Om := Module.Free.of_basis B'
instance OmFinite : Module.Finite ℤ Om := Module.Finite.of_basis B'

noncomputable def timesTableO : TimesTable (Fin 7) ℤ O :=
  timesTableOfSubalgebraBuilderLists T l BQ

noncomputable def B : Basis (Fin 7) ℤ O := timesTableO.basis
def Table : Fin 7 → Fin 7 → List ℤ := 
 ![ ![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], 
 ![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [-1, 1, -1, -1, 0, 0, 3], [0, 0, 1, 0, 2, 0, 1]], 
 ![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [-1, 1, -1, -1, 0, 0, 3], [0, -1, 4, -1, 5, 0, 3], [0, 0, 1, 1, 2, 2, 1]], 
 ![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [-1, 1, -1, -1, 0, 0, 3], [0, -1, 4, -1, 5, 0, 3], [0, 0, 2, 4, 5, 5, 3], [-2, 2, -1, -1, 3, 2, 7]], 
 ![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [-1, 1, -1, -1, 0, 0, 3], [0, -1, 4, -1, 5, 0, 3], [0, 0, 2, 4, 5, 5, 3], [-5, 5, -2, -3, 10, 5, 18], [-2, 0, 7, -3, 13, 3, 13]], 
 ![[0, 0, 0, 0, 0, 1, 0], [-1, 1, -1, -1, 0, 0, 3], [0, -1, 4, -1, 5, 0, 3], [0, 0, 2, 4, 5, 5, 3], [-5, 5, -2, -3, 10, 5, 18], [-5, 0, 18, -7, 33, 10, 33], [-3, 1, 10, 4, 23, 13, 22]], 
 ![[0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 2, 0, 1], [0, 0, 1, 1, 2, 2, 1], [-2, 2, -1, -1, 3, 2, 7], [-2, 0, 7, -3, 13, 3, 13], [-3, 1, 10, 4, 23, 13, 22], [-5, 4, 3, -1, 17, 9, 23]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0, 0, 0] [] (by decide)
instance hp61: Fact $ Nat.Prime 61 := fact_iff.2 (by norm_num)
instance hp62981: Fact $ Nat.Prime 62981 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n := 2
 a' := [1, 3, 0, 0, 3]
 b' := [4, 3, 2, 3, 1, 2]
 k := [4, 4, 3, 0, 2, 1]
 f := [1, 1, 2, 1, 2, 1, 1]
 g := [4, 3, 2, 3, 2, 3, 1]
 h := [1, 1]
 a := [3, 3, 1, 2, 1, 3]
 b := [2, 2, 0, 2, 0, 2]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD61: CertificateDedekindCriterionLists l 61 where
 n := 2
 a' := [15, 37, 43, 33, 17]
 b' := [31, 28, 35, 7, 34, 48]
 k := [4, 46, 47, 56, 49, 1]
 f := [13, 8, 18, 30, 31, 15, 1]
 g := [22, 13, 30, 50, 51, 24, 1]
 h := [36, 1]
 a := [23, 20, 24, 10, 7]
 b := [14, 31, 36, 53, 54]
 c := [34]
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

def CD62981: CertificateDedekindCriterionLists l 62981 where
 n := 2
 a' := [21320, 55173, 11811, 5243, 50696]
 b' := [56444, 1409, 50979, 15332, 56914, 33538]
 k := [7874, 44267, 28567, 58287, 27593, 1]
 f := [3629, 35777, 31602, 36874, 11582, 10774, 1]
 g := [4647, 45813, 40466, 47217, 14830, 13796, 1]
 h := [49184, 1]
 a := [38341, 23216, 33638, 19748, 39972, 1062]
 b := [32985, 41888, 49744, 39508, 20342, 61919]
 c := []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl

noncomputable def D : CertificateDedekindAlmostAllLists T l [3] where
 n := 4
 p := ![3, 5, 61, 62981]
 exp := ![3, 1, 1, 1]
 pdgood := [5, 61, 62981]
 hsub := by decide
 hp := by
  intro i ; fin_cases i
  exact hp3.out
  exact hp5.out
  exact hp61.out
  exact hp62981.out
 a := [-488164191, -641807544, -972531921, -100474494, -56295726, 301252854]
 b := [15242172, 243471279, 152487501, 232635039, 18474336, 14190264, -43036122]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5
  exact satisfiesDedekindCriterion_of_certificate_lists T l 61 T_ofList CD61
  exact satisfiesDedekindCriterion_of_certificate_lists T l 62981 T_ofList CD62981

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 1
 n := 6
 t := 2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [2, 1, 2, 2, 0, 0, 0], [0, 0, 1, 0, 2, 0, 1]], 
![[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [2, 1, 2, 2, 0, 0, 0], [0, 2, 1, 2, 2, 0, 0], [0, 0, 1, 1, 2, 2, 1]], 
![[0, 0, 0, 1, 0, 0, 0], [0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [2, 1, 2, 2, 0, 0, 0], [0, 2, 1, 2, 2, 0, 0], [0, 0, 2, 1, 2, 2, 0], [1, 2, 2, 2, 0, 2, 1]], 
![[0, 0, 0, 0, 1, 0, 0], [0, 0, 0, 0, 0, 1, 0], [2, 1, 2, 2, 0, 0, 0], [0, 2, 1, 2, 2, 0, 0], [0, 0, 2, 1, 2, 2, 0], [1, 2, 1, 0, 1, 2, 0], [1, 0, 1, 0, 1, 0, 1]], 
![[0, 0, 0, 0, 0, 1, 0], [2, 1, 2, 2, 0, 0, 0], [0, 2, 1, 2, 2, 0, 0], [0, 0, 2, 1, 2, 2, 0], [1, 2, 1, 0, 1, 2, 0], [1, 0, 0, 2, 0, 1, 0], [0, 1, 1, 1, 2, 1, 1]], 
![[0, 0, 0, 0, 0, 0, 1], [0, 0, 1, 0, 2, 0, 1], [0, 0, 1, 1, 2, 2, 1], [1, 2, 2, 2, 0, 2, 1], [1, 0, 1, 0, 1, 0, 1], [0, 1, 1, 1, 2, 1, 1], [1, 1, 0, 2, 2, 0, 2]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 1, 0, 1, 2, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0, 0, 0],![2, 2, 1, 2, 0, 0, 1],![1, 0, 0, 0, 0, 0, 1],![2, 0, 1, 1, 0, 0, 0],![2, 1, 1, 2, 1, 0, 2],![2, 1, 0, 0, 1, 0, 2]]
 v := ![![1, 1, 0, 1, 2, 1, 0]]
 w := ![![1, 0, 0, 0, 0, 0, 0],![2, 2, 1, 2, 0, 0, 1],![1, 0, 0, 0, 0, 0, 1],![2, 0, 1, 1, 0, 0, 0],![2, 1, 1, 2, 1, 0, 2],![2, 1, 0, 0, 1, 0, 2]]
 wFrob := ![![1, 0, 0, 0, 0, 0, 0],![0, 1, 0, 0, 0, 0, 1],![0, 0, 1, 0, 0, 0, 1],![0, 0, 0, 1, 0, 0, 0],![0, 0, 0, 0, 1, 0, 2],![0, 0, 0, 0, 0, 1, 2]]
 v_ind := ![0]
 w_ind := ![0, 1, 2, 3, 4, 5]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 2, 2, 1, 1, 2, 1],![0, 4, 4, 2, 4, 2, 0],![0, 4, 4, 2, 4, 2, 4],![0, 2, 2, 0, 2, 2, 2],![0, 1, 0, 2, 1, 1, 0],![0, 1, 2, 1, 2, 2, 1],![1, 2, 0, 0, 0, 2, 1]]
 w1 := ![2]
 w2 := ![0, 0, 1, 2, 0, 2]
 a := ![![1144],![1404],![2280],![1428],![549],![1245],![909]]
 c := ![![-3081, -132, 987, 924, -513, 507],![-4087, -213, 1083, 1308, -669, 753],![-6675, -337, 1911, 2028, -1077, 1221],![-4002, -192, 1210, 1218, -660, 696],![-1512, -78, 456, 448, -234, 261],![-3444, -168, 1056, 1050, -563, 585],![-2328, -90, 801, 678, -393, 364]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inr 3, Sum.inr 4, Sum.inr 5]
 hacindw := by decide 


open BigOperators Classical Matrix Polynomial

lemma B_one : B 0 = 1 := by
  refine basisOfBuilderLists_zero_eq_one _ _ BQ

lemma B_one_repr : B.equivFun.symm ![1, 0, 0, 0, 0, 0, 0] = 1 := by
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

