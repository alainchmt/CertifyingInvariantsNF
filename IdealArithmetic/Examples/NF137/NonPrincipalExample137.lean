import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF137.RI137

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

noncomputable section
instance hq41 : Fact $ Nat.Prime 41 := by decide
instance hq11 : Fact $ Nat.Prime 11 := by decide
instance hq31 : Fact $ Nat.Prime 31 := by decide

def R41 : IsOrderOf (6 : ZMod 41) 40 where
 m := 2
 P := ![2, 5]
 e := ![3, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![11, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![0, -1, 2, 0, 0], ![0, 3, -1, 6, 0], ![0, -4, 2, -1, 12], ![-72, -12, 4, 6, -1]]]
  hmulB := by decide
  f := ![![![4, 73416, -22881, 148302, -864], ![33, -10824, -271755, 792, 0]], ![![2, 73418, -22881, 148302, -864], ![12, -10824, -271755, 792, 0]], ![![2, 40760, -12703, 82336, -480], ![17, -6011, -150876, 440, 0]], ![![2, 32632, -10171, 65917, -384], ![17, -4806, -120789, 352, 0]], ![![2, 13347, -4160, 26964, -157], ![20, -1969, -49410, 144, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-10, 11, 0, 0, 0], ![-5, 0, 11, 0, 0], ![-5, 0, 0, 11, 0], ![-2, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![0, -1, 2, 0, 0], ![-5, 3, -1, 6, 0], ![1, -4, 2, -1, 12], ![0, -12, 4, 6, -1]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 11 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![7, 1, 0, 0, 0], ![0, 7, 2, 0, 0], ![0, 3, 7, 6, 0], ![0, -4, 2, 7, 12], ![-72, -12, 4, 6, 7]]]
  hmulB := by decide
  f := ![![![400058, 485550, 1075594, 930744, -864], ![-1771681, 166129, -4811448, 2232, 0]], ![![133196, 161663, 358128, 309900, -288], ![-589867, 55335, -1602018, 744, 0]], ![![311022, 377497, 836238, 723622, -672], ![-1377380, 129162, -3740739, 1736, 0]], ![![88900, 107906, 239038, 206847, -192], ![-393699, 36923, -1069288, 496, 0]], ![![296824, 360243, 798020, 690552, -641], ![-1314503, 123278, -3569784, 1656, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-7, 31, 0, 0, 0], ![-22, 0, 31, 0, 0], ![-7, 0, 0, 31, 0], ![-23, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![-3, 7, 2, 0, 0], ![-7, 3, 7, 6, 0], ![-11, -4, 2, 7, 12], ![-9, -12, 4, 6, 7]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![4, 1, 0, 0, 0], ![0, 4, 2, 0, 0], ![0, 3, 4, 6, 0], ![0, -4, 2, 4, 12], ![-72, -12, 4, 6, 4]]]
  hmulB := by decide
  f := ![![![3037301, 5918212, 6941008, 10472302, -9744], ![-31132325, 841894, -71582925, 33292, 0]], ![![314220, 612266, 718082, 1083414, -1008], ![-3220754, 87125, -7405625, 3444, 0]], ![![2513621, 4897819, 5744269, 8666712, -8064], ![-25764607, 696734, -59240900, 27552, 0]], ![![1256813, 2448912, 2872140, 4333367, -4032], ![-12882329, 348404, -29620525, 13776, 0]], ![![2815062, 5485170, 6433128, 9706036, -9031], ![-28854376, 780320, -66345150, 30856, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 41, 0, 0, 0], ![-33, 0, 41, 0, 0], ![-17, 0, 0, 41, 0], ![-38, 0, 0, 0, 41]], ![![0, 1, 0, 0, 0], ![-2, 4, 2, 0, 0], ![-6, 3, 4, 6, 0], ![-14, -4, 2, 4, 12], ![-10, -12, 4, 6, 4]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def A3: IdealEqSpanCertificate O ℤ timesTableO I3
 ![![41, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![-19, 1, 0, 0, 0], ![0, -19, 2, 0, 0], ![0, 3, -19, 6, 0], ![0, -4, 2, -19, 12], ![-72, -12, 4, 6, -19]]]
  hmulB := by decide
  f := ![![![-6960440, 1440481, -9575856, 3048186, -6120], ![-15019899, -964894, -20763056, 20910, 0]], ![![-4094138, 847299, -5632484, 1792932, -3600], ![-8834720, -567522, -12212752, 12300, 0]], ![![-818734, 169453, -1126377, 358548, -720], ![-1766742, -113467, -2442288, 2460, 0]], ![![-4913270, 1016820, -6759442, 2151665, -4320], ![-10602321, -681087, -14656304, 14760, 0]], ![![-2546508, 527006, -3503362, 1115190, -2239], ![-5495097, -353009, -7596240, 7650, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-22, 41, 0, 0, 0], ![-4, 0, 41, 0, 0], ![-29, 0, 0, 41, 0], ![-15, 0, 0, 0, 41]], ![![-1, 1, 0, 0, 0], ![10, -19, 2, 0, 0], ![-4, 3, -19, 6, 0], ![11, -4, 2, -19, 12], ![7, -12, 4, 6, -19]]]
  hle1 := by decide
  hle2 := by decide

lemma N3 : Nat.card (O ⧸ I3) = 41 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A3)

def zeta1 := B.equivFun.symm ![113, -54, 0, 22, -22]

def zeta2 := B.equivFun.symm ![28009, 10036, 920, -1530, -2672]

def zeta3 := B.equivFun.symm ![-383105, -37964, 30148, 17252, -40006]

def alpha := B.equivFun.symm ![267863, 87239, 721, -21807, -31202]

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![109, -54, 0, 22, -22] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![53, -54, 0, 22, -22]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![113, -54, 0, 22, -22]
 hxeq :=  rfl
 m:= 4
 C := ![109, -54, 0, 22, -22]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![28001, 10036, 920, -1530, -2672] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-5815, 10036, 920, -1530, -2672]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![28009, 10036, 920, -1530, -2672]
 hxeq :=  rfl
 m:= 8
 C := ![28001, 10036, 920, -1530, -2672]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-383109, -37964, 30148, 17252, -40006] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-14587, -37964, 30148, 17252, -40006]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta3 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-383105, -37964, 30148, 17252, -40006]
 hxeq :=  rfl
 m:= 4
 C := ![-383109, -37964, 30148, 17252, -40006]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log03Mem : IdealMemCertificate O ℤ B I0
  ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![267856, 87239, 721, -21807, -31202] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-39700, 87239, 721, -21807, -31202]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![267863, 87239, 721, -21807, -31202]
 hxeq :=  rfl
 m:= 7
 C := ![267856, 87239, 721, -21807, -31202]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log03Mem
 k :=  7
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] ![107, -54, 0, 22, -22] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![27, -54, 0, 22, -22]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![113, -54, 0, 22, -22]
 hxeq :=  rfl
 m:= 6
 C := ![107, -54, 0, 22, -22]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  25
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] ![27998, 10036, 920, -1530, -2672] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![312, 10036, 920, -1530, -2672]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![28009, 10036, 920, -1530, -2672]
 hxeq :=  rfl
 m:= 11
 C := ![27998, 10036, 920, -1530, -2672]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  23
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] ![-383111, -37964, 30148, 17252, -40006] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![605, -37964, 30148, 17252, -40006]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta3 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-383105, -37964, 30148, 17252, -40006]
 hxeq :=  rfl
 m:= 6
 C := ![-383111, -37964, 30148, 17252, -40006]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  25
 hpow := by decide
 heql := by decide

def Log13Mem : IdealMemCertificate O ℤ B I1
  ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] ![267833, 87239, 721, -21807, -31202] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![16503, 87239, 721, -21807, -31202]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![267863, 87239, 721, -21807, -31202]
 hxeq :=  rfl
 m:= 30
 C := ![267833, 87239, 721, -21807, -31202]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log13Mem
 k :=  15
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] ![101, -54, 0, 22, -22] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![19, -54, 0, 22, -22]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![113, -54, 0, 22, -22]
 hxeq :=  rfl
 m:= 12
 C := ![101, -54, 0, 22, -22]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  27
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] ![27992, 10036, 920, -1530, -2672] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![2074, 10036, 920, -1530, -2672]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![28009, 10036, 920, -1530, -2672]
 hxeq :=  rfl
 m:= 17
 C := ![27992, 10036, 920, -1530, -2672]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  33
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] ![-383137, -37964, 30148, 17252, -40006] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![19, -37964, 30148, 17252, -40006]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta3 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-383105, -37964, 30148, 17252, -40006]
 hxeq :=  rfl
 m:= 32
 C := ![-383137, -37964, 30148, 17252, -40006]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  10
 hpow := by decide
 heql := by decide

def Log23Mem : IdealMemCertificate O ℤ B I2
  ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] ![267836, 87239, 721, -21807, -31202] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![35402, 87239, 721, -21807, -31202]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![267863, 87239, 721, -21807, -31202]
 hxeq :=  rfl
 m:= 27
 C := ![267836, 87239, 721, -21807, -31202]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log23Mem
 k :=  5
 hpow := by decide
 heql := by decide

def Log30Mem : IdealMemCertificate O ℤ B I3
  ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] ![104, -54, 0, 22, -22] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![24, -54, 0, 22, -22]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![113, -54, 0, 22, -22]
 hxeq :=  rfl
 m:= 9
 C := ![104, -54, 0, 22, -22]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log30Mem
 k :=  30
 hpow := by decide
 heql := by decide

def Log31Mem : IdealMemCertificate O ℤ B I3
  ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] ![27969, 10036, 920, -1530, -2672] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-2733, 10036, 920, -1530, -2672]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![28009, 10036, 920, -1530, -2672]
 hxeq :=  rfl
 m:= 40
 C := ![27969, 10036, 920, -1530, -2672]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log31Mem
 k :=  20
 hpow := by decide
 heql := by decide

def Log32Mem : IdealMemCertificate O ℤ B I3
  ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] ![-383119, -37964, 30148, 17252, -40006] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![10519, -37964, 30148, 17252, -40006]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta3 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-383105, -37964, 30148, 17252, -40006]
 hxeq :=  rfl
 m:= 14
 C := ![-383119, -37964, 30148, 17252, -40006]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log32Mem
 k :=  25
 hpow := by decide
 heql := by decide

def Log33Mem : IdealMemCertificate O ℤ B I3
  ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] ![267840, 87239, 721, -21807, -31202] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-13509, 87239, 721, -21807, -31202]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 alpha 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![267863, 87239, 721, -21807, -31202]
 hxeq :=  rfl
 m:= 23
 C := ![267840, 87239, 721, -21807, -31202]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log33Mem
 k :=  36
 hpow := by decide
 heql := by decide

def J : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![-5, -6, -1, 1, 2]] i)))
def MulJ0 : IdealMulEqCertificate O ℤ timesTableO (J) J
  ![![2, 0, 0, 0, 0], ![-5, -6, -1, 1, 2]] ![![2, 0, 0, 0, 0], ![-5, -6, -1, 1, 2]]
  ![![2, 0, 0, 0, 0], ![7, -2, -1, 0, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-10, -12, -2, 2, 4]], ![![-10, -12, -2, 2, 4], ![361, 90, 1, -14, -14]]]
 hmul := by decide
 f :=  ![![![![17107326674067, -9449506302600, -3283131391887, 1283085492523, 4564539858348], ![-7572149476804, 0, 166530654324, 372332856, 383172]], ![![0, 0, 0, 0, 0], ![-18146, 0, -3, 0, 0]]], ![![![-67376370598704448558, 37216419067046674793, 12930452641638361765, -5053369547512454837, -17977217303910123185], ![29822540897135565537, 0, -655872848841339186, -1466414768929458, -1509104229603]], ![![0, 0, 0, 0, 0], ![71467097849, 0, 11815302, 1594, 2]]]]
 g :=  ![![![![-5, 2, 1, 0, -2], ![2, 0, 0, 0, 0]], ![![-11322, -17494, -4298, 2191, 11366], ![-8602, 0, 0, -228, -4]]], ![![![-11322, -17494, -4298, 2191, 11366], ![-8602, 0, 0, -228, -4]], ![![42011, 64935, 15957, -8128, -42191], ![31941, 0, 0, 846, 14]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ1 : IdealMulEqCertificate O ℤ timesTableO (J*J) J
  ![![2, 0, 0, 0, 0], ![7, -2, -1, 0, 2]] ![![2, 0, 0, 0, 0], ![-5, -6, -1, 1, 2]]
  ![![4, 0, 0, 0, 0], ![17, 2, -1, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ0
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0, 0], ![-10, -12, -2, 2, 4]], ![![14, -4, -2, 0, 4], ![85, 23, -1, -5, 4]]]
 hmul := by decide
 f :=  ![![![![-1373655238807662, 758760509802202, 263623341870318, -103027033843003, -366515699337909], ![608015680417996, 0, -13371797465922, -29896892895, -32414631]], ![![0, 0, 0, 0, 0], ![-5381500, 0, 0, 4666, 18]]], ![![![-5951819813588845, 3287583163828944, 1142236119472154, -446399011948827, -1588051601072933], ![2634430875701863, 0, -57937775689665, -129538267296, -140447208]], ![![0, 0, 0, 0, 0], ![-23317145, 0, 0, 20217, 78]]]]
 g :=  ![![![![577320296, 31181911, -63311567, -114058323, 237094119], ![-136308764, -23405646, 26355768, 18792, 1044]], ![![-1340069702, -72379119, 146958134, 264750971, -550340354], ![316398446, 54328939, -61176729, -43620, -2424]]], ![![![2123602052, 114698857, -232883845, -419549573, 872121673], ![-501395106, -86094804, 96946464, 69124, 3840]], ![![12322083443, 665533736, -1351295648, -2434413241, 5060437888], ![-2909317367, -499560348, 562526508, 401089, 22284]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ2 : IdealMulEqCertificate O ℤ timesTableO (J*J*J) J
  ![![4, 0, 0, 0, 0], ![17, 2, -1, 0, 0]] ![![2, 0, 0, 0, 0], ![-5, -6, -1, 1, 2]]
  ![![4, 0, 0, 0, 0], ![-29, -2, 1, 2, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ1
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![-20, -24, -4, 4, 8]], ![![34, 4, -2, 0, 0], ![59, -15, -15, -1, 22]]]
 hmul := by decide
 f :=  ![![![![-6077279310837079733970628, 3356750521758220658324295, 1166635562667256128361731, -455765574347825082050253, -1622145724671465161275112], ![2689600418639031593472596, 0, -59217872781170769936543, -56756206414251689282, -45049240391410269]], ![![-701039734985596680, 0, 0, -544282994963544, -10065692090447], ![29416712036, 0, 68260545, 32170, 18]]], ![![![44566273976472419753261614, -24615926925816762037203491, -8555242808045887766113281, 3342247808029701185569755, 11895617610755220040183088], ![-19723541244937748755518956, 0, 434260103524192800009827, 416208062119554408746, 330357827413896135]], ![![5140907188854936498, 0, 0, 3991369136354400, 73814344959551], ![-215720420443, 0, -500572377, -235911, -132]]]]
 g :=  ![![![![-3413784614, 21063934580, 3359785472, -3967608716, -15255335476], ![20701780960, 4255130856, 0, 3581760, 68880]], ![![7967106635, -49159109738, -7841083161, 9259623909, 35602973790], ![-48313913920, -9930644436, 0, -8359128, -160752]]], ![![![-14792872291, 91275850510, 14558879079, -17192745195, -66105585122], ![89706538778, 18438658098, 0, 15520756, 298476]], ![![-27305504558, 168482029766, 26873586875, -31735323105, -122021357217], ![165585307081, 34035098277, 0, 28649073, 550944]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ3 : IdealMulEqCertificate O ℤ timesTableO (J*J*J*J) J
  ![![4, 0, 0, 0, 0], ![-29, -2, 1, 2, -2]] ![![2, 0, 0, 0, 0], ![-5, -6, -1, 1, 2]]
  ![![267863, 87239, 721, -21807, -31202]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ2
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0, 0], ![-20, -24, -4, 4, 8]], ![![-58, -4, 2, 4, -4], ![-119, -45, -5, 13, 12]]]
 hmul := by decide
 f :=  ![![![![1638144403667384889191008184029, -904819714966297335434370488065, -314469276763255166223549764495, 122852664924936643425876304194, 437253061468755267761863505176], ![-724987831956719044087832456342, 0, 15962309634339351127116495811, 15300342111813190887845768, 6986702903399855696998]], ![![-960501712961555530668, 0, 0, 894319914671390121, 5728776409721512], ![9223133591471, 0, 0, 3556484430, 1204302]]]]
 g :=  ![![![![-19880, -1609, 1506, 750, -1880]], ![![-12748, -8980, 2161, 3848, -5676]]], ![![![-24950, -4268, 2226, 1898, -3628]], ![![91415, -16132, -3389, 6524, -4594]]]]
 hle1 := by decide
 hle2 := by decide

lemma J5 : J ^ 5 =  Ideal.span {alpha} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate O ℤ timesTableO _ _ _ _ _ MulJ3, alpha]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![-9487, -3242, -280, 514, 826])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![276889, -1012, -11072, -12390, 23912])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta3 : IsUnit zeta3 := by 
 apply isUnit_of_mul_eq_one _ (B.equivFun.symm ![3198898752415, 1041910152748, 8679201204, -260365018060, -372576911846])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

