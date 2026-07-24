import IdealArithmetic.Examples.NF5_3_5695312500_2.ClassGroupData5_3_5695312500_2
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_3_5695312500_2.RI5_3_5695312500_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat2 
instance hq11 : Fact $ Nat.Prime 11 := {out := by norm_num}
instance hq3 : Fact $ Nat.Prime 3 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R3 : IsOrderOf (2 : ZMod 3) 2 where
 m := 1
 P := ![2]
 e := ![1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] i)))
def I4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 2, 0], ![-38, -14, -9, -28, 83], ![-12, -5, -1, -8, 27]]]
  hmulB := by decide  
  f := ![![![39, 24, -43, -84, -83], ![-30, -12, 168, 3, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, 0, -1, -1, 0], ![0, 1, 2, 0, 0]], ![![26, 16, -29, -56, -55], ![-20, -7, 112, 2, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 1, 2, 0], ![-68, -14, -9, -28, 83], ![-22, -5, -1, -8, 27]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 2, 2, 0], ![-38, -14, -9, -27, 83], ![-12, -5, -1, -8, 28]]]
  hmulB := by decide  
  f := ![![![111, -15, -98, 21, -83], ![-504, 707, 21, 7, 0]], ![![108, -14, -95, 21, -83], ![-489, 686, 21, 7, 0]], ![![111, -13, -96, 21, -83], ![-505, 694, 21, 7, 0]], ![![0, -2, -3, -1, 0], ![1, 13, 4, 0, 0]], ![![96, -12, -84, 18, -71], ![-438, 606, 18, 6, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![-1, 0, 0, 7, 0], ![-6, 0, 0, 0, 7]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-2, 0, 2, 2, 0], ![-63, -14, -9, -27, 83], ![-23, -5, -1, -8, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![-3, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-3, 1, 0, 0, 0], ![0, -3, 1, 0, 0], ![0, 0, -2, 2, 0], ![-38, -14, -9, -31, 83], ![-12, -5, -1, -8, 24]]]
  hmulB := by decide  
  f := ![![![19609, -19408, 4911, 113, -1245], ![44422, -30968, 1232, 105, 0]], ![![13068, -12930, 3271, 76, -830], ![29604, -20629, 819, 70, 0]], ![![19595, -19394, 4906, 115, -1245], ![44390, -30946, 1225, 105, 0]], ![![13075, -12938, 3274, 75, -830], ![29620, -20642, 823, 70, 0]], ![![16809, -16635, 4208, 98, -1067], ![38079, -26542, 1052, 90, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-4, 7, 0, 0, 0], ![-5, 0, 7, 0, 0], ![-5, 0, 0, 7, 0], ![-6, 0, 0, 0, 7]], ![![-1, 1, 0, 0, 0], ![1, -3, 1, 0, 0], ![0, 0, -2, 2, 0], ![-40, -14, -9, -31, 83], ![-13, -5, -1, -8, 24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def A3: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![5, 1, 0, 0, 0], ![0, 5, 1, 0, 0], ![0, 0, 6, 2, 0], ![-38, -14, -9, -23, 83], ![-12, -5, -1, -8, 32]]]
  hmulB := by decide  
  f := ![![![10966, 774, 68856, 23353, -1245], ![-22869, 3333, -126544, 165, 0]], ![![6572, 462, 41311, 14011, -747], ![-13705, 2002, -75922, 99, 0]], ![![8764, 614, 55077, 18680, -996], ![-18276, 2674, -101222, 132, 0]], ![![8770, 617, 55086, 18683, -996], ![-18289, 2670, -101238, 132, 0]], ![![5976, 417, 37557, 12738, -679], ![-12462, 1827, -69024, 90, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-5, 11, 0, 0, 0], ![-8, 0, 11, 0, 0], ![-9, 0, 0, 11, 0], ![-6, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-3, 5, 1, 0, 0], ![-6, 0, 6, 2, 0], ![-17, -14, -9, -23, 83], ![-9, -5, -1, -8, 32]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N3 : Nat.card (O ⧸ I3) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)

def A4: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 0, 2, 2, 0], ![-38, -14, -9, -27, 83], ![-12, -5, -1, -8, 28]]]
  hmulB := by decide  
  f := ![![![0, -4, -5, -2, 0], ![3, 9, 3, 0, 0]], ![![0, -2, -2, 0, 0], ![1, 6, 0, 0, 0]], ![![0, -2, -3, -2, 0], ![2, 4, 3, 0, 0]], ![![0, -1, 2, 3, 0], ![1, 2, -4, 0, 0]], ![![-33, 1, 27, -5, 28], ![61, -78, -6, -1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![-1, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-2, 0, 2, 2, 0], ![7, -14, -9, -27, 83], ![1, -5, -1, -8, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N4 : Nat.card (O ⧸ I4) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4)

def Log00Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-4631, 546, -3982, -3216, 8528] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-7229, 546, -3982, -3216, 8528]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4629, 546, -3982, -3216, 8528]
 hxeq :=  rfl
 m := 2
 C := ![-4631, 546, -3982, -3216, 8528]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![24435, -3151, 21323, 16824, -44838] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![38037, -3151, 21323, 16824, -44838]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![24437, -3151, 21323, 16824, -44838]
 hxeq :=  rfl
 m := 2
 C := ![24435, -3151, 21323, 16824, -44838]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-474918, -10979, -332883, -369502, 919008] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-770978, -10979, -332883, -369502, 919008]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-474917, -10979, -332883, -369502, 919008]
 hxeq :=  rfl
 m := 1
 C := ![-474918, -10979, -332883, -369502, 919008]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log03Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-3, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log03Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log04Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-8, 3, -8, -5, 11] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-10, 3, -8, -5, 11]
 hmem := by decide

def Log04: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-7, 3, -8, -5, 11]
 hxeq :=  rfl
 m := 1
 C := ![-8, 3, -8, -5, 11]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log04Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-4633, 546, -3982, -3216, 8528] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-4177, 546, -3982, -3216, 8528]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4629, 546, -3982, -3216, 8528]
 hxeq :=  rfl
 m := 4
 C := ![-4633, 546, -3982, -3216, 8528]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![24434, -3151, 21323, 16824, -44838] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![21693, -3151, 21323, 16824, -44838]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![24437, -3151, 21323, 16824, -44838]
 hxeq :=  rfl
 m := 3
 C := ![24434, -3151, 21323, 16824, -44838]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-474919, -10979, -332883, -369502, 919008] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-515884, -10979, -332883, -369502, 919008]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-474917, -10979, -332883, -369502, 919008]
 hxeq :=  rfl
 m := 2
 C := ![-474919, -10979, -332883, -369502, 919008]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log13Mem : IdealMemCertificate B I1
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-7, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 6
 C := ![-7, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log13Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log14Mem : IdealMemCertificate B I1
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-12, 3, -8, -5, 11] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-4, 3, -8, -5, 11]
 hmem := by decide

def Log14: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-7, 3, -8, -5, 11]
 hxeq :=  rfl
 m := 5
 C := ![-12, 3, -8, -5, 11]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log14Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-4632, 546, -3982, -3216, 8528] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-3142, 546, -3982, -3216, 8528]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4629, 546, -3982, -3216, 8528]
 hxeq :=  rfl
 m := 3
 C := ![-4632, 546, -3982, -3216, 8528]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![24435, -3151, 21323, 16824, -44838] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![16476, -3151, 21323, 16824, -44838]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![24437, -3151, 21323, 16824, -44838]
 hxeq :=  rfl
 m := 2
 C := ![24435, -3151, 21323, 16824, -44838]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-474923, -10979, -332883, -369502, 919008] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-347590, -10979, -332883, -369502, 919008]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-474917, -10979, -332883, -369502, 919008]
 hxeq :=  rfl
 m := 6
 C := ![-474923, -10979, -332883, -369502, 919008]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log23Mem : IdealMemCertificate B I2
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-7, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 6
 C := ![-7, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log23Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log24Mem : IdealMemCertificate B I2
 ![![7, 0, 0, 0, 0], ![4, 1, 0, 0, 0], ![5, 0, 1, 0, 0], ![5, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-8, 3, -8, -5, 11] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-3, 3, -8, -5, 11]
 hmem := by decide

def Log24: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-7, 3, -8, -5, 11]
 hxeq :=  rfl
 m := 1
 C := ![-8, 3, -8, -5, 11]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log24Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log30Mem : IdealMemCertificate B I3
 ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-4636, 546, -3982, -3216, 8528] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![206, 546, -3982, -3216, 8528]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4629, 546, -3982, -3216, 8528]
 hxeq :=  rfl
 m := 7
 C := ![-4636, 546, -3982, -3216, 8528]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log30Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log31Mem : IdealMemCertificate B I3
 ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![24435, -3151, 21323, 16824, -44838] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1162, -3151, 21323, 16824, -44838]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![24437, -3151, 21323, 16824, -44838]
 hxeq :=  rfl
 m := 2
 C := ![24435, -3151, 21323, 16824, -44838]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log31Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log32Mem : IdealMemCertificate B I3
 ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-474924, -10979, -332883, -369502, 919008] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![4955, -10979, -332883, -369502, 919008]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-474917, -10979, -332883, -369502, 919008]
 hxeq :=  rfl
 m := 7
 C := ![-474924, -10979, -332883, -369502, 919008]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log32Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log33Mem : IdealMemCertificate B I3
 ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-11, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 10
 C := ![-11, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log33Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log34Mem : IdealMemCertificate B I3
 ![![11, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![8, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![6, 0, 0, 0, 1]] ![-17, 3, -8, -5, 11] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![1, 3, -8, -5, 11]
 hmem := by decide

def Log34: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-7, 3, -8, -5, 11]
 hxeq :=  rfl
 m := 10
 C := ![-17, 3, -8, -5, 11]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log34Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log40Mem : IdealMemCertificate B I4
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-4631, 546, -3982, -3216, 8528] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![2001, 546, -3982, -3216, 8528]
 hmem := by decide

def Log40: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4629, 546, -3982, -3216, 8528]
 hxeq :=  rfl
 m := 2
 C := ![-4631, 546, -3982, -3216, 8528]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log40Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log41Mem : IdealMemCertificate B I4
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![24435, -3151, 21323, 16824, -44838] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-10628, -3151, 21323, 16824, -44838]
 hmem := by decide

def Log41: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![24437, -3151, 21323, 16824, -44838]
 hxeq :=  rfl
 m := 2
 C := ![24435, -3151, 21323, 16824, -44838]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log41Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log42Mem : IdealMemCertificate B I4
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-474918, -10979, -332883, -369502, 919008] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![190443, -10979, -332883, -369502, 919008]
 hmem := by decide

def Log42: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-474917, -10979, -332883, -369502, 919008]
 hxeq :=  rfl
 m := 1
 C := ![-474918, -10979, -332883, -369502, 919008]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log42Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log43Mem : IdealMemCertificate B I4
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log43: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-3, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log43Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log44Mem : IdealMemCertificate B I4
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![1, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-9, 3, -8, -5, 11] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![3, 3, -8, -5, 11]
 hmem := by decide

def Log44: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-7, 3, -8, -5, 11]
 hxeq :=  rfl
 m := 2
 C := ![-9, 3, -8, -5, 11]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log44Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

end Sat2
