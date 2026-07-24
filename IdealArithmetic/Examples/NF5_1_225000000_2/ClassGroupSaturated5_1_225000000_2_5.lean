import IdealArithmetic.Examples.NF5_1_225000000_2.ClassGroupData5_1_225000000_2
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_225000000_2.RI5_1_225000000_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq41 : Fact $ Nat.Prime 41 := {out := by norm_num}
instance hq61 : Fact $ Nat.Prime 61 := {out := by norm_num}
instance hq71 : Fact $ Nat.Prime 71 := {out := by norm_num}

def R41 : IsOrderOf (6 : ZMod 41) 40 where
 m := 2
 P := ![2, 5]
 e := ![3, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R61 : IsOrderOf (2 : ZMod 61) 60 where
 m := 3
 P := ![2, 3, 5]
 e := ![2, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R71 : IsOrderOf (7 : ZMod 71) 70 where
 m := 3
 P := ![2, 5, 7]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![-14, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0, 0, 0, 0], ![34, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![41, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]] 
 ![![41, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] where
  M :=![![![41, 0, 0, 0, 0], ![0, 41, 0, 0, 0], ![0, 0, 41, 0, 0], ![0, 0, 0, 41, 0], ![0, 0, 0, 0, 41]], ![![-5, 1, 0, 0, 0], ![0, -5, 1, 0, 0], ![0, 1, -5, 2, 0], ![6, 7, 2, -3, 12], ![0, -5, 2, -2, -7]]]
  hmulB := by decide  
  f := ![![![1006668, -953290, 3876099, -1552752, 3024], ![8242271, 180195, 31815918, -10332, 0]], ![![898806, -851150, 3460796, -1386383, 2700], ![7359132, 160884, 28407014, -9225, 0]], ![![395480, -374504, 1522746, -610007, 1188], ![3238062, 70808, 12499055, -4059, 0]], ![![539282, -510690, 2076483, -831832, 1620], ![4415466, 96537, 17044254, -5535, 0]], ![![908456, -860286, 3497943, -1401264, 2729], ![7438143, 162615, 28711926, -9324, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-36, 41, 0, 0, 0], ![-16, 0, 41, 0, 0], ![-22, 0, 0, 41, 0], ![-37, 0, 0, 0, 41]], ![![-1, 1, 0, 0, 0], ![4, -5, 1, 0, 0], ![0, 1, -5, 2, 0], ![-16, 7, 2, -3, 12], ![11, -5, 2, -2, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 41 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![-14, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![-14, 1, 0, 0, 0], ![0, -14, 1, 0, 0], ![0, 1, -14, 2, 0], ![6, 7, 2, -12, 12], ![0, -5, 2, -2, -16]]]
  hmulB := by decide  
  f := ![![![68001043, -16453633, 180148421, -25765180, 17172], ![296252844, 5520317, 785314244, -87291, 0]], ![![52604629, -12728296, 139360223, -19931572, 13284], ![229176940, 4270427, 607507784, -67527, 0]], ![![53887600, -13038730, 142759058, -20417680, 13608], ![234766322, 4374555, 622324196, -69174, 0]], ![![42340284, -10244717, 112167888, -16042471, 10692], ![184459370, 3437174, 488969260, -54351, 0]], ![![65771485, -15914177, 174241916, -24920420, 16609], ![286539568, 5339286, 759566236, -84429, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-47, 61, 0, 0, 0], ![-48, 0, 61, 0, 0], ![-38, 0, 0, 61, 0], ![-59, 0, 0, 0, 61]], ![![-1, 1, 0, 0, 0], ![10, -14, 1, 0, 0], ![9, 1, -14, 2, 0], ![-11, 7, 2, -12, 12], ![19, -5, 2, -2, -16]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 61 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![71, 0, 0, 0, 0], ![34, 1, 0, 0, 0]] 
 ![![71, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![71, 0, 0, 0, 0], ![0, 71, 0, 0, 0], ![0, 0, 71, 0, 0], ![0, 0, 0, 71, 0], ![0, 0, 0, 0, 71]], ![![34, 1, 0, 0, 0], ![0, 34, 1, 0, 0], ![0, 1, 34, 2, 0], ![6, 7, 2, 36, 12], ![0, -5, 2, -2, 32]]]
  hmulB := by decide  
  f := ![![![108669917, 10619598, 398550101, 23533944, 27540], ![-226899599, 9016787, -832522002, -162945, 0]], ![![53269552, 5205664, 195367644, 11536244, 13500], ![-111225262, 4420034, -408098912, -79875, 0]], ![![78838905, 7704411, 289144061, 17073638, 19980], ![-164613321, 6541586, -603986279, -118215, 0]], ![![59661899, 5830336, 218811824, 12920597, 15120], ![-124572295, 4950458, -457070913, -89460, 0]], ![![13775035, 1346134, 50520435, 2983176, 3491], ![-28761869, 1142997, -105530958, -20655, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-34, 71, 0, 0, 0], ![-51, 0, 71, 0, 0], ![-39, 0, 0, 71, 0], ![-9, 0, 0, 0, 71]], ![![0, 1, 0, 0, 0], ![-17, 34, 1, 0, 0], ![-26, 1, 34, 2, 0], ![-26, 7, 2, 36, 12], ![-2, -5, 2, -2, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 71 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![41, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] ![1608, 830, 1218, 991, 2364] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-3830, 830, 1218, 991, 2364]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1640, 830, 1218, 991, 2364]
 hxeq :=  rfl
 m := 32
 C := ![1608, 830, 1218, 991, 2364]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 10
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![41, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] ![-159, 209, -93, -18, -98] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-53, 209, -93, -18, -98]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-133, 209, -93, -18, -98]
 hxeq :=  rfl
 m := 26
 C := ![-159, 209, -93, -18, -98]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 17
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![41, 0, 0, 0, 0], ![36, 1, 0, 0, 0], ![16, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![37, 0, 0, 0, 1]] ![2414, -2032, 692, 138, 851] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![731, -2032, 692, 138, 851]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2422, -2032, 692, 138, 851]
 hxeq :=  rfl
 m := 8
 C := ![2414, -2032, 692, 138, 851]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 38
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![61, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] ![1633, 830, 1218, 991, 2364] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-4475, 830, 1218, 991, 2364]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1640, 830, 1218, 991, 2364]
 hxeq :=  rfl
 m := 7
 C := ![1633, 830, 1218, 991, 2364]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 49
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![61, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] ![-192, 209, -93, -18, -98] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![15, 209, -93, -18, -98]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-133, 209, -93, -18, -98]
 hxeq :=  rfl
 m := 59
 C := ![-192, 209, -93, -18, -98]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 31
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![61, 0, 0, 0, 0], ![47, 1, 0, 0, 0], ![48, 0, 1, 0, 0], ![38, 0, 0, 1, 0], ![59, 0, 0, 0, 1]] ![2376, -2032, 692, 138, 851] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![151, -2032, 692, 138, 851]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2422, -2032, 692, 138, 851]
 hxeq :=  rfl
 m := 46
 C := ![2376, -2032, 692, 138, 851]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 58
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![71, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![1589, 830, 1218, 991, 2364] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-2094, 830, 1218, 991, 2364]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R71) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1640, 830, 1218, 991, 2364]
 hxeq :=  rfl
 m := 51
 C := ![1589, 830, 1218, 991, 2364]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![71, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![-144, 209, -93, -18, -98] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-13, 209, -93, -18, -98]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R71) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-133, 209, -93, -18, -98]
 hxeq :=  rfl
 m := 11
 C := ![-144, 209, -93, -18, -98]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 31
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![71, 0, 0, 0, 0], ![34, 1, 0, 0, 0], ![51, 0, 1, 0, 0], ![39, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![2391, -2032, 692, 138, 851] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![326, -2032, 692, 138, 851]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R71) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2422, -2032, 692, 138, 851]
 hxeq :=  rfl
 m := 31
 C := ![2391, -2032, 692, 138, 851]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 11
 hpow := by zmod_pow
 heql := by decide

end Sat5
