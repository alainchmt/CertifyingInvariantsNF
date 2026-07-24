import IdealArithmetic.Examples.NF3_1_387059_1.ClassGroupData3_1_387059_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_387059_1.RI3_1_387059_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat11 
instance hq67 : Fact $ Nat.Prime 67 := {out := by norm_num}
instance hq199 : Fact $ Nat.Prime 199 := {out := by norm_num}

def R67 : IsOrderOf (2 : ZMod 67) 66 where
 m := 3
 P := ![2, 3, 11]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R199 : IsOrderOf (3 : ZMod 199) 198 where
 m := 3
 P := ![2, 3, 11]
 e := ![1, 2, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![67, 0, 0], ![-28, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![199, 0, 0], ![-48, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![67, 0, 0], ![-28, 1, 0]] 
 ![![67, 0, 0], ![39, 1, 0], ![32, 0, 1]] where
  M :=![![![67, 0, 0], ![0, 67, 0], ![0, 0, 67]], ![![-28, 1, 0], ![2, -29, 4], ![8, -30, -26]]]
  hmulB := by decide  
  f := ![![![3421, -63765, 8800], ![-2345, -147400, 0]], ![![2001, -37100, 5120], ![-1339, -85760, 0]], ![![1636, -30455, 4203], ![-1115, -70400, 0]]]
  g := ![![![1, 0, 0], ![-39, 67, 0], ![-32, 0, 67]], ![![-1, 1, 0], ![15, -29, 4], ![30, -30, -26]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 67 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![199, 0, 0], ![-48, 1, 0]] 
 ![![199, 0, 0], ![151, 1, 0], ![109, 0, 1]] where
  M :=![![![199, 0, 0], ![0, 199, 0], ![0, 0, 199]], ![![-48, 1, 0], ![2, -49, 4], ![8, -30, -46]]]
  hmulB := by decide  
  f := ![![![-4913, 132143, -10788], ![1990, 536703, 0]], ![![-3707, 100246, -8184], ![1593, 407154, 0]], ![![-2699, 72380, -5909], ![1057, 293973, 0]]]
  g := ![![![1, 0, 0], ![-151, 199, 0], ![-109, 0, 199]], ![![-1, 1, 0], ![35, -49, 4], ![48, -30, -46]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 199 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![67, 0, 0], ![39, 1, 0], ![32, 0, 1]] ![-46, 3, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 3, -3]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R67) ▸ IsPrimitiveRoot.orderOf _) 11 zeta1 6 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2, 3, -3]
 hxeq :=  rfl
 m := 44
 C := ![-46, 3, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 61
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![67, 0, 0], ![39, 1, 0], ![32, 0, 1]] ![-7, 4, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 4, -3]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R67) ▸ IsPrimitiveRoot.orderOf _) 11 alpha0 4 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2, 4, -3]
 hxeq :=  rfl
 m := 5
 C := ![-7, 4, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 15
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![199, 0, 0], ![151, 1, 0], ![109, 0, 1]] ![-73, 3, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 3, -3]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R199) ▸ IsPrimitiveRoot.orderOf _) 11 zeta1 5 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2, 3, -3]
 hxeq :=  rfl
 m := 71
 C := ![-73, 3, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 49
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![199, 0, 0], ![151, 1, 0], ![109, 0, 1]] ![-121, 4, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-2, 4, -3]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R199) ▸ IsPrimitiveRoot.orderOf _) 11 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-2, 4, -3]
 hxeq :=  rfl
 m := 119
 C := ![-121, 4, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 67
 hpow := by zmod_pow
 heql := by decide

end Sat11
