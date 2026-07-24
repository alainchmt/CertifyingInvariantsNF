import IdealArithmetic.Examples.NF3_1_644799_1.ClassGroupData3_1_644799_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_644799_1.RI3_1_644799_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat2 
instance hq3 : Fact $ Nat.Prime 3 := {out := by norm_num}
instance hq5 : Fact $ Nat.Prime 5 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R3 : IsOrderOf (2 : ZMod 3) 2 where
 m := 1
 P := ![2]
 e := ![1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R5 : IsOrderOf (2 : ZMod 5) 4 where
 m := 1
 P := ![2]
 e := ![2]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 0, 1]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![0, 0, 1]] 
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 0, 1], ![-156, 1, 3], ![-87, -17, 3]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![52, 0, -1], ![0, 1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 0, 1], ![-52, 1, 3], ![-29, -17, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![3, 0, 0], ![-1, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![-1, 1, 0], ![-3, -3, 9], ![-156, 1, 2]]]
  hmulB := by decide  
  f := ![![![568, 53, -8], ![-171, 0, 12]], ![![285, 26, -4], ![-83, 0, 6]], ![![379, 35, -5], ![-113, 0, 8]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-2, 0, 3]], ![![-1, 1, 0], ![-5, -3, 9], ![-54, 1, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![5, 0, 0], ![1, 1, 0]] 
 ![![5, 0, 0], ![1, 1, 0], ![2, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![1, 1, 0], ![-3, -1, 9], ![-156, 1, 4]]]
  hmulB := by decide  
  f := ![![![-8, -3, 27], ![0, -15, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-4, -2, 11], ![4, -6, 0]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-2, 0, 5]], ![![0, 1, 0], ![-4, -1, 9], ![-33, 1, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 5 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def A3: IdealEqSpanCertificate' Table ![![7, 0, 0], ![2, 1, 0]] 
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![-3, 0, 9], ![-156, 1, 5]]]
  hmulB := by decide  
  f := ![![![45, -2, -144], ![14, 112, 0]], ![![10, -1, -36], ![8, 28, 0]], ![![12, -1, -41], ![7, 32, 0]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![-2, 0, 7]], ![![0, 1, 0], ![-3, 0, 9], ![-24, 1, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N3 : Nat.card (O ⧸ I3) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)

def Log00Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] ![543, -26, -71] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![181, -26, -71]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![545, -26, -71]
 hxeq :=  rfl
 m := 2
 C := ![543, -26, -71]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] ![-3, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 0]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-3, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] ![762, -71, 26] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![254, -71, 26]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![763, -71, 26]
 hxeq :=  rfl
 m := 1
 C := ![762, -71, 26]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log03Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![0, 1, 0], ![0, 0, 1]] ![54, 5, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![18, 5, 0]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![56, 5, 0]
 hxeq :=  rfl
 m := 2
 C := ![54, 5, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log03Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] ![544, -26, -71] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![246, -26, -71]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![545, -26, -71]
 hxeq :=  rfl
 m := 1
 C := ![544, -26, -71]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] ![-3, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-3, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] ![762, -71, 26] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![284, -71, 26]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![763, -71, 26]
 hxeq :=  rfl
 m := 1
 C := ![762, -71, 26]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log13Mem : IdealMemCertificate B I1
 ![![3, 0, 0], ![2, 1, 0], ![2, 0, 1]] ![55, 5, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![15, 5, 0]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![56, 5, 0]
 hxeq :=  rfl
 m := 1
 C := ![55, 5, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log13Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![5, 0, 0], ![1, 1, 0], ![2, 0, 1]] ![542, -26, -71] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![142, -26, -71]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![545, -26, -71]
 hxeq :=  rfl
 m := 3
 C := ![542, -26, -71]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![5, 0, 0], ![1, 1, 0], ![2, 0, 1]] ![-5, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, 0]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 4
 C := ![-5, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![5, 0, 0], ![1, 1, 0], ![2, 0, 1]] ![761, -71, 26] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![156, -71, 26]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![763, -71, 26]
 hxeq :=  rfl
 m := 2
 C := ![761, -71, 26]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log23Mem : IdealMemCertificate B I2
 ![![5, 0, 0], ![1, 1, 0], ![2, 0, 1]] ![55, 5, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![10, 5, 0]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![56, 5, 0]
 hxeq :=  rfl
 m := 1
 C := ![55, 5, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log23Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log30Mem : IdealMemCertificate B I3
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] ![541, -26, -71] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![105, -26, -71]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![545, -26, -71]
 hxeq :=  rfl
 m := 4
 C := ![541, -26, -71]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log30Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log31Mem : IdealMemCertificate B I3
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] ![-7, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 0, 0]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 6
 C := ![-7, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log31Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log32Mem : IdealMemCertificate B I3
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] ![757, -71, 26] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![121, -71, 26]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![763, -71, 26]
 hxeq :=  rfl
 m := 6
 C := ![757, -71, 26]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log32Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log33Mem : IdealMemCertificate B I3
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] ![52, 5, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![6, 5, 0]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![56, 5, 0]
 hxeq :=  rfl
 m := 4
 C := ![52, 5, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log33Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

end Sat2
