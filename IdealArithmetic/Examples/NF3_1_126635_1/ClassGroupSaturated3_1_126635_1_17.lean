import IdealArithmetic.Examples.NF3_1_126635_1.ClassGroupData3_1_126635_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_126635_1.RI3_1_126635_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat17 
instance hq103 : Fact $ Nat.Prime 103 := {out := by norm_num}

def R103 : IsOrderOf (5 : ZMod 103) 102 where
 m := 3
 P := ![2, 3, 17]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![18, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![41, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![18, 1, 0]] 
 ![![103, 0, 0], ![18, 1, 0], ![92, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![18, 1, 0], ![0, 19, 3], ![-72, 7, 18]]]
  hmulB := by decide  
  f := ![![![955, 53, 0], ![-5459, 0, 0]], ![![162, 9, 0], ![-926, 0, 0]], ![![860, 35, -2], ![-4916, 69, 0]]]
  g := ![![![1, 0, 0], ![-18, 103, 0], ![-92, 0, 103]], ![![0, 1, 0], ![-6, 19, 3], ![-18, 7, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 103 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![103, 0, 0], ![41, 1, 0]] 
 ![![103, 0, 0], ![41, 1, 0], ![44, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![41, 1, 0], ![0, 42, 3], ![-72, 7, 41]]]
  hmulB := by decide  
  f := ![![![3199, 78, 0], ![-8034, 0, 0]], ![![1271, 31, 0], ![-3192, 0, 0]], ![![1400, 6, -2], ![-3516, 69, 0]]]
  g := ![![![1, 0, 0], ![-41, 103, 0], ![-44, 0, 103]], ![![0, 1, 0], ![-18, 42, 3], ![-21, 7, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 103 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![103, 0, 0], ![18, 1, 0], ![92, 0, 1]] ![-149, -14, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![1, -14, 0]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R103) ▸ IsPrimitiveRoot.orderOf _) 17 zeta1 8 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-95, -14, 0]
 hxeq :=  rfl
 m := 54
 C := ![-149, -14, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 59
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![103, 0, 0], ![18, 1, 0], ![92, 0, 1]] ![226, -58, 25] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-10, -58, 25]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R103) ▸ IsPrimitiveRoot.orderOf _) 17 alpha0 8 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![280, -58, 25]
 hxeq :=  rfl
 m := 54
 C := ![226, -58, 25]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 59
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![103, 0, 0], ![41, 1, 0], ![44, 0, 1]] ![-162, -14, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![4, -14, 0]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R103) ▸ IsPrimitiveRoot.orderOf _) 17 zeta1 13 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-95, -14, 0]
 hxeq :=  rfl
 m := 67
 C := ![-162, -14, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 13
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![103, 0, 0], ![41, 1, 0], ![44, 0, 1]] ![267, -58, 25] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![15, -58, 25]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R103) ▸ IsPrimitiveRoot.orderOf _) 17 alpha0 4 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![280, -58, 25]
 hxeq :=  rfl
 m := 13
 C := ![267, -58, 25]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 72
 hpow := by zmod_pow
 heql := by decide

end Sat17
