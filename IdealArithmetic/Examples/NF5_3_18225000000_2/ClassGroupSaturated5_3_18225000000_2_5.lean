import IdealArithmetic.Examples.NF5_3_18225000000_2.ClassGroupData5_3_18225000000_2
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_3_18225000000_2.RI5_3_18225000000_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq41 : Fact $ Nat.Prime 41 := {out := by norm_num}
instance hq11 : Fact $ Nat.Prime 11 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

def R41 : IsOrderOf (6 : ZMod 41) 40 where
 m := 2
 P := ![2, 5]
 e := ![3, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![0, -1, 2, 0, 0], ![0, 3, -1, 6, 0], ![0, -4, 2, -1, 12], ![-72, -12, 4, 6, -1]]]
  hmulB := by decide  
  f := ![![![4, 73416, -22881, 148302, -864], ![33, -10824, -271755, 792, 0]], ![![2, 73418, -22881, 148302, -864], ![12, -10824, -271755, 792, 0]], ![![2, 40760, -12703, 82336, -480], ![17, -6011, -150876, 440, 0]], ![![2, 32632, -10171, 65917, -384], ![17, -4806, -120789, 352, 0]], ![![2, 13347, -4160, 26964, -157], ![20, -1969, -49410, 144, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-10, 11, 0, 0, 0], ![-5, 0, 11, 0, 0], ![-5, 0, 0, 11, 0], ![-2, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![0, -1, 2, 0, 0], ![-5, 3, -1, 6, 0], ![1, -4, 2, -1, 12], ![0, -12, 4, 6, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![7, 1, 0, 0, 0], ![0, 7, 2, 0, 0], ![0, 3, 7, 6, 0], ![0, -4, 2, 7, 12], ![-72, -12, 4, 6, 7]]]
  hmulB := by decide  
  f := ![![![400058, 485550, 1075594, 930744, -864], ![-1771681, 166129, -4811448, 2232, 0]], ![![133196, 161663, 358128, 309900, -288], ![-589867, 55335, -1602018, 744, 0]], ![![311022, 377497, 836238, 723622, -672], ![-1377380, 129162, -3740739, 1736, 0]], ![![88900, 107906, 239038, 206847, -192], ![-393699, 36923, -1069288, 496, 0]], ![![296824, 360243, 798020, 690552, -641], ![-1314503, 123278, -3569784, 1656, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-7, 31, 0, 0, 0], ![-22, 0, 31, 0, 0], ![-7, 0, 0, 31, 0], ![-23, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![-3, 7, 2, 0, 0], ![-7, 3, 7, 6, 0], ![-11, -4, 2, 7, 12], ![-9, -12, 4, 6, 7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![4, 1, 0, 0, 0], ![0, 4, 2, 0, 0], ![0, 3, 4, 6, 0], ![0, -4, 2, 4, 12], ![-72, -12, 4, 6, 4]]]
  hmulB := by decide  
  f := ![![![3037301, 5918212, 6941008, 10472302, -9744], ![-31132325, 841894, -71582925, 33292, 0]], ![![314220, 612266, 718082, 1083414, -1008], ![-3220754, 87125, -7405625, 3444, 0]], ![![2513621, 4897819, 5744269, 8666712, -8064], ![-25764607, 696734, -59240900, 27552, 0]], ![![1256813, 2448912, 2872140, 4333367, -4032], ![-12882329, 348404, -29620525, 13776, 0]], ![![2815062, 5485170, 6433128, 9706036, -9031], ![-28854376, 780320, -66345150, 30856, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 41, 0, 0, 0], ![-33, 0, 41, 0, 0], ![-17, 0, 0, 41, 0], ![-38, 0, 0, 0, 41]], ![![0, 1, 0, 0, 0], ![-2, 4, 2, 0, 0], ![-6, 3, 4, 6, 0], ![-14, -4, 2, 4, 12], ![-10, -12, 4, 6, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 41 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def A3: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![-19, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![-19, 1, 0, 0, 0], ![0, -19, 2, 0, 0], ![0, 3, -19, 6, 0], ![0, -4, 2, -19, 12], ![-72, -12, 4, 6, -19]]]
  hmulB := by decide  
  f := ![![![-6960440, 1440481, -9575856, 3048186, -6120], ![-15019899, -964894, -20763056, 20910, 0]], ![![-4094138, 847299, -5632484, 1792932, -3600], ![-8834720, -567522, -12212752, 12300, 0]], ![![-818734, 169453, -1126377, 358548, -720], ![-1766742, -113467, -2442288, 2460, 0]], ![![-4913270, 1016820, -6759442, 2151665, -4320], ![-10602321, -681087, -14656304, 14760, 0]], ![![-2546508, 527006, -3503362, 1115190, -2239], ![-5495097, -353009, -7596240, 7650, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-22, 41, 0, 0, 0], ![-4, 0, 41, 0, 0], ![-29, 0, 0, 41, 0], ![-15, 0, 0, 0, 41]], ![![-1, 1, 0, 0, 0], ![10, -19, 2, 0, 0], ![-4, 3, -19, 6, 0], ![11, -4, 2, -19, 12], ![7, -12, 4, 6, -19]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N3 : Nat.card (O ⧸ I3) = 41 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)

def Log00Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![109, -54, 0, 22, -22] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![53, -54, 0, 22, -22]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![113, -54, 0, 22, -22]
 hxeq :=  rfl
 m := 4
 C := ![109, -54, 0, 22, -22]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-28012, -10036, -920, 1530, 2672] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![5814, -10036, -920, 1530, 2672]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-28009, -10036, -920, 1530, 2672]
 hxeq :=  rfl
 m := 3
 C := ![-28012, -10036, -920, 1530, 2672]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![383098, 37964, -30148, -17252, 40006] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![14586, 37964, -30148, -17252, 40006]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta3 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![383105, 37964, -30148, -17252, 40006]
 hxeq :=  rfl
 m := 7
 C := ![383098, 37964, -30148, -17252, 40006]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log03Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![267856, 87239, 721, -21807, -31202] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-39700, 87239, 721, -21807, -31202]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![267863, 87239, 721, -21807, -31202]
 hxeq :=  rfl
 m := 7
 C := ![267856, 87239, 721, -21807, -31202]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log03Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] ![107, -54, 0, 22, -22] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![27, -54, 0, 22, -22]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![113, -54, 0, 22, -22]
 hxeq :=  rfl
 m := 6
 C := ![107, -54, 0, 22, -22]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 25
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] ![-28029, -10036, -920, 1530, 2672] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-313, -10036, -920, 1530, 2672]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-28009, -10036, -920, 1530, 2672]
 hxeq :=  rfl
 m := 20
 C := ![-28029, -10036, -920, 1530, 2672]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] ![383080, 37964, -30148, -17252, 40006] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-606, 37964, -30148, -17252, 40006]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta3 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![383105, 37964, -30148, -17252, 40006]
 hxeq :=  rfl
 m := 25
 C := ![383080, 37964, -30148, -17252, 40006]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 10
 hpow := by zmod_pow
 heql := by decide

def Log13Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![22, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![23, 0, 0, 0, 1]] ![267833, 87239, 721, -21807, -31202] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![16503, 87239, 721, -21807, -31202]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![267863, 87239, 721, -21807, -31202]
 hxeq :=  rfl
 m := 30
 C := ![267833, 87239, 721, -21807, -31202]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log13Mem
 k := 15
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] ![101, -54, 0, 22, -22] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![19, -54, 0, 22, -22]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![113, -54, 0, 22, -22]
 hxeq :=  rfl
 m := 12
 C := ![101, -54, 0, 22, -22]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 27
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] ![-28033, -10036, -920, 1530, 2672] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-2075, -10036, -920, 1530, 2672]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-28009, -10036, -920, 1530, 2672]
 hxeq :=  rfl
 m := 24
 C := ![-28033, -10036, -920, 1530, 2672]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 13
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] ![383096, 37964, -30148, -17252, 40006] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-20, 37964, -30148, -17252, 40006]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta3 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![383105, 37964, -30148, -17252, 40006]
 hxeq :=  rfl
 m := 9
 C := ![383096, 37964, -30148, -17252, 40006]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 30
 hpow := by zmod_pow
 heql := by decide

def Log23Mem : IdealMemCertificate B I2
 ![![41, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![33, 0, 1, 0, 0], ![17, 0, 0, 1, 0], ![38, 0, 0, 0, 1]] ![267836, 87239, 721, -21807, -31202] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![35402, 87239, 721, -21807, -31202]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![267863, 87239, 721, -21807, -31202]
 hxeq :=  rfl
 m := 27
 C := ![267836, 87239, 721, -21807, -31202]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log23Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log30Mem : IdealMemCertificate B I3
 ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] ![104, -54, 0, 22, -22] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![24, -54, 0, 22, -22]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![113, -54, 0, 22, -22]
 hxeq :=  rfl
 m := 9
 C := ![104, -54, 0, 22, -22]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log30Mem
 k := 30
 hpow := by zmod_pow
 heql := by decide

def Log31Mem : IdealMemCertificate B I3
 ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] ![-28010, -10036, -920, 1530, 2672] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![2732, -10036, -920, 1530, 2672]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-28009, -10036, -920, 1530, 2672]
 hxeq :=  rfl
 m := 1
 C := ![-28010, -10036, -920, 1530, 2672]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log31Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log32Mem : IdealMemCertificate B I3
 ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] ![383078, 37964, -30148, -17252, 40006] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-10520, 37964, -30148, -17252, 40006]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta3 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![383105, 37964, -30148, -17252, 40006]
 hxeq :=  rfl
 m := 27
 C := ![383078, 37964, -30148, -17252, 40006]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log32Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log33Mem : IdealMemCertificate B I3
 ![![41, 0, 0, 0, 0], ![22, 1, 0, 0, 0], ![4, 0, 1, 0, 0], ![29, 0, 0, 1, 0], ![15, 0, 0, 0, 1]] ![267840, 87239, 721, -21807, -31202] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-13509, 87239, 721, -21807, -31202]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![267863, 87239, 721, -21807, -31202]
 hxeq :=  rfl
 m := 23
 C := ![267840, 87239, 721, -21807, -31202]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log33Mem
 k := 36
 hpow := by zmod_pow
 heql := by decide

end Sat5
