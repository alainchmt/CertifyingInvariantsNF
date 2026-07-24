import IdealArithmetic.Examples.NF3_1_767839_1.ClassGroupData3_1_767839_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_767839_1.RI3_1_767839_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat2 
instance hq11 : Fact $ Nat.Prime 11 := {out := by norm_num}
instance hq5 : Fact $ Nat.Prime 5 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-3, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![1, 1, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![0, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-3, 1, 0]] 
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-3, 1, 0], ![0, -3, 1], ![155, -31, -3]]]
  hmulB := by decide  
  f := ![![![22, -7, 0], ![49, 0, 0]], ![![4, 14, -5], ![8, 35, 0]], ![![14, -4, 0], ![31, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 7, 0], ![-5, 0, 7]], ![![-1, 1, 0], ![1, -3, 1], ![42, -31, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![1, 1, 0]] 
 ![![11, 0, 0], ![1, 1, 0], ![10, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![1, 1, 0], ![0, 1, 1], ![155, -31, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![11, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, 0], ![10, 1, 0]]]
  g := ![![![1, 0, 0], ![-1, 11, 0], ![-10, 0, 11]], ![![0, 1, 0], ![-1, 1, 1], ![16, -31, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![5, 0, 0], ![0, 1, 0]] 
 ![![5, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![0, 0, 1], ![155, -31, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![0, 1, 0], ![0, 0, 1], ![31, -31, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 5 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] ![-1466017, 332843, 22449] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-415662, 332843, 22449]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1466016, 332843, 22449]
 hxeq :=  rfl
 m := 1
 C := ![-1466017, 332843, 22449]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] ![-7, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 0]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
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
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![4, 1, 0], ![5, 0, 1]] ![216197, 17609, 4956] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![17283, 17609, 4956]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![216202, 17609, 4956]
 hxeq :=  rfl
 m := 5
 C := ![216197, 17609, 4956]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![11, 0, 0], ![1, 1, 0], ![10, 0, 1]] ![-1466018, 332843, 22449] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-183941, 332843, 22449]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1466016, 332843, 22449]
 hxeq :=  rfl
 m := 2
 C := ![-1466018, 332843, 22449]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![11, 0, 0], ![1, 1, 0], ![10, 0, 1]] ![-11, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 10
 C := ![-11, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![11, 0, 0], ![1, 1, 0], ![10, 0, 1]] ![216197, 17609, 4956] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![13548, 17609, 4956]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![216202, 17609, 4956]
 hxeq :=  rfl
 m := 5
 C := ![216197, 17609, 4956]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![5, 0, 0], ![0, 1, 0], ![0, 0, 1]] ![-1466020, 332843, 22449] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-293204, 332843, 22449]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1466016, 332843, 22449]
 hxeq :=  rfl
 m := 4
 C := ![-1466020, 332843, 22449]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![5, 0, 0], ![0, 1, 0], ![0, 0, 1]] ![-5, 0, 0] where
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
 ![![5, 0, 0], ![0, 1, 0], ![0, 0, 1]] ![216200, 17609, 4956] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![43240, 17609, 4956]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![216202, 17609, 4956]
 hxeq :=  rfl
 m := 2
 C := ![216200, 17609, 4956]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

end Sat2
