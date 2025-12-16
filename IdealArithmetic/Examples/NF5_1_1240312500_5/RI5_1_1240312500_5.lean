
import IdealArithmetic.CertificateDedekind
import IdealArithmetic.CertifyAdjoinRoot
import Mathlib.Tactic.NormNum.Prime
import IdealArithmetic.MaximalAPI
import Mathlib.NumberTheory.NumberField.Basic
import IdealArithmetic.Examples.NF5_1_1240312500_5.Irreducible5_1_1240312500_5
import IdealArithmetic.DiscriminantSubalgebraBuilder



open Polynomial

noncomputable def T : ℤ[X] := X^5 - 10*X^2 - 285*X + 774 
lemma T_def : T = X^5 - 10*X^2 - 285*X + 774 := rfl

def K := AdjoinRoot (map (algebraMap ℤ ℚ) T)

noncomputable instance : CommRing K := by
  unfold K
  infer_instance

noncomputable instance : Algebra ℚ K := by
  unfold K
  infer_instance

local notation "l" => [774, -285, -10, 0, 0, 1]

noncomputable def Adj : IsAdjoinRoot K (map (algebraMap ℤ ℚ) T) :=
   AdjoinRoot.isAdjoinRoot _
   
local notation "θ" => Adj.root

lemma T_ofList : ofList l = T := by
  rw [T_def] ; norm_num ; ring

-- We build the subalgebra with integral basis [1, a, a^2, 1/2*a^3 - 1/2*a, 1/252*a^4 + 17/84*a^3 + 9/28*a^2 + 89/252*a - 5/42] 

noncomputable def BQ : SubalgebraBuilderLists 5 ℤ  ℚ K T l where
 d :=  252
 hlen := rfl
 htr := rfl
 hofL := T_ofList.symm
 hm := rfl
 B := ![![252, 0, 0, 0, 0], ![0, 252, 0, 0, 0], ![0, 0, 252, 0, 0], ![0, -126, 0, 126, 0], ![-30, 89, 81, 51, 1]]
 a := ![ ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 0, 0, 1, 0],![0, 0, 0, 0, 1]], 
![![0, 1, 0, 0, 0],![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![15, -70, -41, -51, 126],![3, -27, -16, -20, 51]], 
![![0, 0, 1, 0, 0],![0, 1, 0, 2, 0],![30, -140, -81, -102, 252],![-387, 142, 5, -1, 0],![-147, 10, -23, -32, 81]], 
![![0, 0, 0, 1, 0],![15, -70, -41, -51, 126],![-387, 142, 5, -1, 0],![-15, -121, 112, 56, -126],![-120, -45, 21, -7, 24]], 
![![0, 0, 0, 0, 1],![3, -27, -16, -20, 51],![-147, 10, -23, -32, 81],![-120, -45, 21, -7, 24],![-95, -32, -9, -25, 67]]]
 s := ![![[], [], [], [], []],![[], [], [], [], [-252]],![[], [], [], [-31752], [-12852, -252]],![[], [], [-31752], [0, -15876], [-10080, -6426, -126]],![[], [-252], [-12852, -252], [-10080, -6426, -126], [-8450, -2763, -102, -1]]]
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
 ![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [15, -70, -41, -51, 126], [3, -27, -16, -20, 51]], 
 ![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [30, -140, -81, -102, 252], [-387, 142, 5, -1, 0], [-147, 10, -23, -32, 81]], 
 ![[0, 0, 0, 1, 0], [15, -70, -41, -51, 126], [-387, 142, 5, -1, 0], [-15, -121, 112, 56, -126], [-120, -45, 21, -7, 24]], 
 ![[0, 0, 0, 0, 1], [3, -27, -16, -20, 51], [-147, 10, -23, -32, 81], [-120, -45, 21, -7, 24], [-95, -32, -9, -25, 67]]]

lemma timesTableT_eq_Table :  ∀ i j , Table i j = List.ofFn (timesTableO.table i j) := by decide

lemma hroot_mem : θ ∈ O := by
  refine root_in_subalgebra_lists T l BQ ![0, 1, 0, 0, 0] [] (by decide)

instance hp2: Fact $ Nat.Prime 2 := fact_iff.2 (by norm_num)
instance hp3: Fact $ Nat.Prime 3 := fact_iff.2 (by norm_num)
instance hp5: Fact $ Nat.Prime 5 := fact_iff.2 (by norm_num)
instance hp7: Fact $ Nat.Prime 7 := fact_iff.2 (by norm_num)

def CD5: CertificateDedekindCriterionLists l 5 where
 n :=  5
 a' := []
 b' :=  [1]
 k := [1]
 f := [-154, 58, 3, 1, 1]
 g :=  [4, 1]
 h :=  [1, 1, 1, 1, 1]
 a :=  [4]
 b :=  [3, 0, 2, 1]
 c :=  []
 hdvdpow := rfl
 hcop := rfl
 hf := by rfl
 habc := by rfl 

noncomputable def D : CertificateDedekindAlmostAllLists T l [2, 3, 7] where
 n := 4
 p := ![2, 3, 5, 7]
 exp := ![8, 8, 7, 4]
 pdgood := [5]
 hsub := by decide
 hp := by
  intro i ; fin_cases i 
  exact hp2.out
  exact hp3.out
  exact hp5.out
  exact hp7.out
 a := [1200622500000, 428652000000, 136930500000, 43659000000]
 b := [2155167000000, -187733700000, -85730400000, -27386100000, -8731800000]
 hab := by decide
 hd := by 
  intro p hp 
  fin_cases hp 
  exact satisfiesDedekindCriterion_of_certificate_lists T l 5 T_ofList CD5

noncomputable def M2 : MaximalOrderCertificateWLists 2 O Om hm where
 m := 2
 n := 3
 t :=  3
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [1, 0, 1, 1, 0], [1, 1, 0, 0, 1]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [1, 0, 1, 1, 0], [1, 0, 1, 0, 1]], 
![[0, 0, 0, 1, 0], [1, 0, 1, 1, 0], [1, 0, 1, 1, 0], [1, 1, 0, 0, 0], [0, 1, 1, 1, 0]], 
![[0, 0, 0, 0, 1], [1, 1, 0, 0, 1], [1, 0, 1, 0, 1], [0, 1, 1, 1, 0], [1, 0, 1, 1, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 1, 1, 0],![0, 1, 1, 0, 0]]
 b2 := ![![1, 0, 0, 0, 0],![1, 0, 0, 0, 1],![0, 1, 0, 0, 0]]
 v := ![![1, 0, 1, 1, 0],![0, 1, 1, 0, 0]]
 w := ![![1, 0, 0, 0, 0],![1, 0, 0, 0, 1],![0, 1, 0, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 1, 1],![0, 0, 1, 0, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![1, 1, 1, 0, 0],![0, 1, 0, 0, 1],![1, 0, 0, 1, 1],![0, 1, 0, 1, 1],![0, 0, 1, 1, 1]]
 w1 := ![1, 0]
 w2 := ![0, 1, 1]
 a := ![![-251, 62],![-218, 95],![-186, 212],![-276, 230],![-350, 256]]
 c := ![![-510, 322, -78],![-392, 286, -184],![-697, 260, -286],![-756, 373, -356],![-1148, 466, -297]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M3 : MaximalOrderCertificateWLists 3 O Om hm where
 m := 2
 n := 3
 t :=  2
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 2, 1, 0, 0], [0, 0, 2, 1, 0]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [0, 1, 0, 0, 0], [0, 1, 2, 2, 0], [0, 1, 1, 1, 0]], 
![[0, 0, 0, 1, 0], [0, 2, 1, 0, 0], [0, 1, 2, 2, 0], [0, 2, 1, 2, 0], [0, 0, 0, 2, 0]], 
![[0, 0, 0, 0, 1], [0, 0, 2, 1, 0], [0, 1, 1, 1, 0], [0, 0, 0, 2, 0], [1, 1, 0, 2, 1]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 b2 := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 1]]
 v := ![![0, 1, 2, 0, 0],![0, 0, 0, 1, 0]]
 w := ![![1, 0, 0, 0, 0],![0, 1, 0, 0, 0],![0, 1, 0, 0, 1]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 2, 0],![0, 0, 1, 1, 1]]
 v_ind := ![1, 3]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![2, 2, 0, 2, 0],![2, 4, 2, 4, 0],![2, 2, 2, 0, 0],![0, 2, 4, 2, 0],![0, 0, 2, 2, 2]]
 w1 := ![0, 1]
 w2 := ![0, 1, 0]
 a := ![![-49, -294],![-93, -580],![-33, -90],![-39, -276],![-33, -318]]
 c := ![![30, -501, 252],![-198, -909, 504],![-248, -21, 84],![-486, -313, 252],![-312, -483, 286]]
 hmulw := by decide 
 ac_indw := ![Sum.inl 0, Sum.inl 1, Sum.inr 0, Sum.inr 1, Sum.inr 2]
 hacindw := by decide 

noncomputable def M7 : MaximalOrderCertificateWLists 7 O Om hm where
 m := 2
 n := 3
 t :=  1
 hpos := by decide
 TT := timesTableO
 B' := B'
 T := Table
 heq := timesTableT_eq_Table
 TMod := ![![[1, 0, 0, 0, 0], [0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 0, 0, 1, 0], [0, 0, 0, 0, 1]], 
![[0, 1, 0, 0, 0], [0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [1, 0, 1, 5, 0], [3, 1, 5, 1, 2]], 
![[0, 0, 1, 0, 0], [0, 1, 0, 2, 0], [2, 0, 3, 3, 0], [5, 2, 5, 6, 0], [0, 3, 5, 3, 4]], 
![[0, 0, 0, 1, 0], [1, 0, 1, 5, 0], [5, 2, 5, 6, 0], [6, 5, 0, 0, 0], [6, 4, 0, 0, 3]], 
![[0, 0, 0, 0, 1], [3, 1, 5, 1, 2], [0, 3, 5, 3, 4], [6, 4, 0, 0, 3], [3, 3, 5, 3, 4]]]
 hTMod := by decide
 hle := by decide
 b1 := ![![1, 0, 0, 5, 6],![0, 1, 3, 3, 6]]
 b2 := ![![1, 0, 0, 0, 0],![2, 6, 1, 0, 0],![1, 4, 6, 0, 0]]
 v := ![![1, 0, 0, 5, 6],![0, 1, 3, 3, 6]]
 w := ![![1, 0, 0, 0, 0],![2, 6, 1, 0, 0],![1, 4, 6, 0, 0]]
 wFrob := ![![1, 0, 0, 0, 0],![0, 1, 0, 3, 0],![0, 0, 1, 5, 0]]
 v_ind := ![0, 1]
 w_ind := ![0, 1, 2]
 hmod1 := by decide
 hmod2 := by decide
 hindv := by decide
 hindw := by decide
 hvFrobKer := by decide
 hwFrobComp := by decide 
 g := ![![40, 0, 40, 16, 32],![640, 0, 256, 256, 384],![0, 64, 0, 32, 0],![8, 16, 32, 0, 0],![160, 96, 0, 32, 0]]
 w1 := ![1, 1]
 w2 := ![1, 0, 1]
 a := ![![-329552, 452256],![-2797088, 3841504],![-85568, 118496],![-188216, 258216],![-107296, 149184]]
 c := ![![-37121, 10570, -38731],![-759507, 103670, -326585],![-70579, 4662, -9849],![24325, 4614, -22337],![-64743, 5054, -12309]]
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

lemma B_int_repr {n : ℤ} : B.equivFun.symm ![n, 0,0,0,0] = n := by
  suffices B.equivFun.symm ![n, 0,0,0,0] = n • 1 by convert this ; simp only [zsmul_eq_mul,mul_one]
  rw [← B_one_repr, ← LinearEquiv.map_smul]
  simp only [Basis.equivFun_symm_apply, zsmul_eq_mul, Matrix.smul_cons, smul_eq_mul, mul_one,
    mul_zero, Matrix.smul_empty]

instance : IsDomain O := by
  haveI hirr : Fact $ Irreducible (map (algebraMap ℤ ℚ) T) :=
  {out := (Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map (T_monic)).1 T_irreducible}
  letI hola : Field K := by
    unfold K
    exact AdjoinRoot.instField
  haveI : IsDomain K := by infer_instance
  refine Subalgebra.isDomain O 
