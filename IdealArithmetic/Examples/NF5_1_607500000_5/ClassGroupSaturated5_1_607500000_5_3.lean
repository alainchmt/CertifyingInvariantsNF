import IdealArithmetic.Examples.NF5_1_607500000_5.ClassGroupData5_1_607500000_5
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_607500000_5.RI5_1_607500000_5

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq37 : Fact $ Nat.Prime 37 := {out := by norm_num}
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R37 : IsOrderOf (2 : ZMod 37) 36 where
 m := 2
 P := ![2, 3]
 e := ![2, 2]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R7 : IsOrderOf (3 : ZMod 7) 6 where
 m := 2
 P := ![2, 3]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![-2, -1, -4, 7, 0], ![0, -1, -1, 2, 2], ![10, -5, 11, -13, -1]]]
  hmulB := by decide  
  f := ![![![662, -2235, -1402, 3066, 3426], ![2527, 28, 0, -12096, -210]], ![![662, -2235, -1402, 3066, 3426], ![2528, 28, 0, -12096, -210]], ![![662, -2232, -1399, 3060, 3420], ![2528, 29, 0, -12075, -210]], ![![364, -1226, -768, 1680, 1877], ![1394, 14, 0, -6627, -115]], ![![190, -639, -401, 876, 979], ![728, 11, 0, -3456, -60]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![-4, 0, 0, 7, 0], ![-2, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, -1, -4, 7, 0], ![0, -1, -1, 2, 2], ![4, -5, 11, -13, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![-2, -1, -1, 7, 0], ![0, -1, -1, 5, 2], ![10, -5, 11, -13, 2]]]
  hmulB := by decide  
  f := ![![![-119325, -60937, -5249, 32188, -128], ![715247, 8697, -60372, 832, 0]], ![![-29910, -15275, -1316, 8068, -32], ![179284, 2184, -15132, 208, 0]], ![![-89417, -45663, -3933, 24120, -96], ![535975, 6514, -45240, 624, 0]], ![![-44757, -22857, -1969, 12073, -48], ![268279, 3265, -22644, 312, 0]], ![![-55074, -28126, -2423, 14856, -59], ![330120, 4019, -27864, 384, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 13, 0, 0, 0], ![-9, 0, 13, 0, 0], ![-5, 0, 0, 13, 0], ![-6, 0, 0, 0, 13]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-2, -1, -1, 7, 0], ![-2, -1, -1, 5, 2], ![-2, -5, 11, -13, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0]] 
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] where
  M :=![![![37, 0, 0, 0, 0], ![0, 37, 0, 0, 0], ![0, 0, 37, 0, 0], ![0, 0, 0, 37, 0], ![0, 0, 0, 0, 37]], ![![9, 1, 0, 0, 0], ![0, 9, 1, 0, 0], ![-2, -1, 6, 7, 0], ![0, -1, -1, 12, 2], ![10, -5, 11, -13, 9]]]
  hmulB := by decide  
  f := ![![![-91781774, -11343018, 1440336, 1807857, 768], ![375206973, 3882114, -9531459, -14208, 0]], ![![-22939830, -2835069, 359995, 451854, 192], ![93778795, 970325, -2382282, -3552, 0]], ![![-74573166, -9216264, 1170280, 1468893, 624], ![304857606, 3154251, -7744359, -11544, 0]], ![![-17208830, -2126792, 270058, 338968, 144], ![70350275, 727916, -1787121, -2664, 0]], ![![-81859422, -10116746, 1284624, 1612413, 685], ![334644065, 3462426, -8501031, -12672, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 37, 0, 0, 0], ![-30, 0, 37, 0, 0], ![-7, 0, 0, 37, 0], ![-33, 0, 0, 0, 37]], ![![0, 1, 0, 0, 0], ![-3, 9, 1, 0, 0], ![-6, -1, 6, 7, 0], ![-3, -1, -1, 12, 2], ![-13, -5, 11, -13, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 37 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![732564, -518780, 105501, -76167, 48164] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![488654, -518780, 105501, -76167, 48164]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![732565, -518780, 105501, -76167, 48164]
 hxeq :=  rfl
 m := 1
 C := ![732564, -518780, 105501, -76167, 48164]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-43067, 19747, -1913, 6064, -38] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-24893, 19747, -1913, 6064, -38]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-43063, 19747, -1913, 6064, -38]
 hxeq :=  rfl
 m := 4
 C := ![-43067, 19747, -1913, 6064, -38]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![7, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![514, -169, -6, -80, -17] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![274, -169, -6, -80, -17]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![515, -169, -6, -80, -17]
 hxeq :=  rfl
 m := 1
 C := ![514, -169, -6, -80, -17]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![732555, -518780, 105501, -76167, 48164] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![70189, -518780, 105501, -76167, 48164]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![732565, -518780, 105501, -76167, 48164]
 hxeq :=  rfl
 m := 10
 C := ![732555, -518780, 105501, -76167, 48164]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 10
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-43064, 19747, -1913, 6064, -38] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-7341, 19747, -1913, 6064, -38]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-43063, 19747, -1913, 6064, -38]
 hxeq :=  rfl
 m := 1
 C := ![-43064, 19747, -1913, 6064, -38]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![9, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![510, -169, -6, -80, -17] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![108, -169, -6, -80, -17]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![515, -169, -6, -80, -17]
 hxeq :=  rfl
 m := 5
 C := ![510, -169, -6, -80, -17]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] ![732553, -518780, 105501, -76167, 48164] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![31900, -518780, 105501, -76167, 48164]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![732565, -518780, 105501, -76167, 48164]
 hxeq :=  rfl
 m := 12
 C := ![732553, -518780, 105501, -76167, 48164]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 28
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] ![-43083, 19747, -1913, 6064, -38] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-5530, 19747, -1913, 6064, -38]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-43063, 19747, -1913, 6064, -38]
 hxeq :=  rfl
 m := 20
 C := ![-43083, 19747, -1913, 6064, -38]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 25
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![37, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![30, 0, 1, 0, 0], ![7, 0, 0, 1, 0], ![33, 0, 0, 0, 1]] ![508, -169, -6, -80, -17] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![90, -169, -6, -80, -17]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![515, -169, -6, -80, -17]
 hxeq :=  rfl
 m := 7
 C := ![508, -169, -6, -80, -17]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 32
 hpow := by zmod_pow
 heql := by decide

end Sat3
