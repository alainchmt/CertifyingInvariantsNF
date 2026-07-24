import IdealArithmetic.Examples.NF3_1_948300_2.ClassGroupData3_1_948300_2
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_948300_2.RI3_1_948300_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq19 : Fact $ Nat.Prime 19 := {out := by norm_num}
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}

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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![3, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-2, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![3, 1, 0]] 
 ![![19, 0, 0], ![3, 1, 0], ![2, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![3, 1, 0], ![-1, 4, 3], ![197, 20, 2]]]
  hmulB := by decide  
  f := ![![![-119, 467, 351], ![19, -2223, 0]], ![![-18, 72, 54], ![1, -342, 0]], ![![-13, 49, 37], ![5, -234, 0]]]
  g := ![![![1, 0, 0], ![-3, 19, 0], ![-2, 0, 19]], ![![0, 1, 0], ![-1, 4, 3], ![7, 20, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 19 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-2, 1, 0]] 
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-2, 1, 0], ![-1, -1, 3], ![197, 20, -3]]]
  hmulB := by decide  
  f := ![![![-45, -49, 144], ![13, -624, 0]], ![![-37, -41, 120], ![14, -520, 0]], ![![-42, -45, 133], ![9, -576, 0]]]
  g := ![![![1, 0, 0], ![-11, 13, 0], ![-12, 0, 13]], ![![-1, 1, 0], ![-2, -1, 3], ![1, 20, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![19, 0, 0], ![3, 1, 0], ![2, 0, 1]] ![-447655111913397114, -48952286427462266, 27713281222931533] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-18748674477730178, -48952286427462266, 27713281222931533]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-447655111913397110, -48952286427462266, 27713281222931533]
 hxeq :=  rfl
 m := 4
 C := ![-447655111913397114, -48952286427462266, 27713281222931533]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![19, 0, 0], ![3, 1, 0], ![2, 0, 1]] ![1426700314, 309682724, 79240070] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![17851158, 309682724, 79240070]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1426700321, 309682724, 79240070]
 hxeq :=  rfl
 m := 7
 C := ![1426700314, 309682724, 79240070]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] ![-447655111913397115, -48952286427462266, 27713281222931533] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-18595333529730045, -48952286427462266, 27713281222931533]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-447655111913397110, -48952286427462266, 27713281222931533]
 hxeq :=  rfl
 m := 5
 C := ![-447655111913397115, -48952286427462266, 27713281222931533]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![13, 0, 0], ![11, 1, 0], ![12, 0, 1]] ![1426700314, 309682724, 79240070] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-225437730, 309682724, 79240070]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1426700321, 309682724, 79240070]
 hxeq :=  rfl
 m := 7
 C := ![1426700314, 309682724, 79240070]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 11
 hpow := by zmod_pow
 heql := by decide

end Sat3
