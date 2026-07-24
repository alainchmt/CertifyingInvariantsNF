import IdealArithmetic.Examples.NF3_1_780332_1.ClassGroupData3_1_780332_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_780332_1.RI3_1_780332_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq19 : Fact $ Nat.Prime 19 := {out := by norm_num}
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R19 : IsOrderOf (2 : ZMod 19) 18 where
 m := 2
 P := ![2, 3]
 e := ![1, 2]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-3, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-5, 1, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![9, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-3, 1, 0]] 
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-3, 1, 0], ![0, -3, 1], ![558, 124, -3]]]
  hmulB := by decide  
  f := ![![![22, -7, 0], ![49, 0, 0]], ![![4, 14, -5], ![8, 35, 0]], ![![14, -4, 0], ![31, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 7, 0], ![-5, 0, 7]], ![![-1, 1, 0], ![1, -3, 1], ![11, 124, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-5, 1, 0]] 
 ![![13, 0, 0], ![8, 1, 0], ![1, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-5, 1, 0], ![0, -5, 1], ![558, 124, -5]]]
  hmulB := by decide  
  f := ![![![51, -10, 0], ![130, 0, 0]], ![![36, -7, 0], ![92, 0, 0]], ![![7, -1, 0], ![18, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 13, 0], ![-1, 0, 13]], ![![-1, 1, 0], ![3, -5, 1], ![-33, 124, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![19, 0, 0], ![9, 1, 0]] 
 ![![19, 0, 0], ![9, 1, 0], ![14, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![9, 1, 0], ![0, 9, 1], ![558, 124, 9]]]
  hmulB := by decide  
  f := ![![![46, 5, 0], ![-95, 0, 0]], ![![18, 2, 0], ![-37, 0, 0]], ![![32, 3, 0], ![-66, 1, 0]]]
  g := ![![![1, 0, 0], ![-9, 19, 0], ![-14, 0, 19]], ![![0, 1, 0], ![-5, 9, 1], ![-36, 124, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 19 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] ![44012, 7818, -868] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![2440, 7818, -868]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![44015, 7818, -868]
 hxeq :=  rfl
 m := 3
 C := ![44012, 7818, -868]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] ![-225735, -67622, -5230] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![10129, -67622, -5230]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-225729, -67622, -5230]
 hxeq :=  rfl
 m := 6
 C := ![-225735, -67622, -5230]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] ![10, -1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![2, -1, 0]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![13, -1, 0]
 hxeq :=  rfl
 m := 3
 C := ![10, -1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![13, 0, 0], ![8, 1, 0], ![1, 0, 1]] ![44009, 7818, -868] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1359, 7818, -868]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![44015, 7818, -868]
 hxeq :=  rfl
 m := 6
 C := ![44009, 7818, -868]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![13, 0, 0], ![8, 1, 0], ![1, 0, 1]] ![-225730, -67622, -5230] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![24652, -67622, -5230]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-225729, -67622, -5230]
 hxeq :=  rfl
 m := 1
 C := ![-225730, -67622, -5230]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![13, 0, 0], ![8, 1, 0], ![1, 0, 1]] ![5, -1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![1, -1, 0]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![13, -1, 0]
 hxeq :=  rfl
 m := 8
 C := ![5, -1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![19, 0, 0], ![9, 1, 0], ![14, 0, 1]] ![43998, 7818, -868] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-748, 7818, -868]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![44015, 7818, -868]
 hxeq :=  rfl
 m := 17
 C := ![43998, 7818, -868]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 10
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![19, 0, 0], ![9, 1, 0], ![14, 0, 1]] ![-225742, -67622, -5230] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![24004, -67622, -5230]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-225729, -67622, -5230]
 hxeq :=  rfl
 m := 13
 C := ![-225742, -67622, -5230]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![19, 0, 0], ![9, 1, 0], ![14, 0, 1]] ![10, -1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![1, -1, 0]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![13, -1, 0]
 hxeq :=  rfl
 m := 3
 C := ![10, -1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 13
 hpow := by zmod_pow
 heql := by decide

end Sat3
