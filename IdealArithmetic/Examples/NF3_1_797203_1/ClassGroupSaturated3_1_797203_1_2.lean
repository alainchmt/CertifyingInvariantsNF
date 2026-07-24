import IdealArithmetic.Examples.NF3_1_797203_1.ClassGroupData3_1_797203_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_797203_1.RI3_1_797203_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat2 
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}
instance hq3 : Fact $ Nat.Prime 3 := {out := by norm_num}
instance hq5 : Fact $ Nat.Prime 5 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![2, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![3, 1, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-4, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![2, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![2, 1, 0], ![2, 1, 4], ![152, -26, 4]]]
  hmulB := by decide  
  f := ![![![-1, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 3], ![2, -2, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![0, 1, 4], ![68, -26, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-1, 1, 0]] 
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-1, 1, 0], ![2, -2, 4], ![152, -26, 1]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![4, 2, 0]]]
  g := ![![![1, 0, 0], ![-6, 7, 0], ![0, 0, 7]], ![![-1, 1, 0], ![2, -2, 4], ![44, -26, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![5, 0, 0], ![3, 1, 0]] 
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![3, 1, 0], ![2, 2, 4], ![152, -26, 5]]]
  hmulB := by decide  
  f := ![![![-8, -11, -24], ![-5, 30, 0]], ![![-6, -6, -12], ![1, 15, 0]], ![![-7, -9, -19], ![-3, 24, 0]]]
  g := ![![![1, 0, 0], ![-3, 5, 0], ![-4, 0, 5]], ![![0, 1, 0], ![-4, 2, 4], ![42, -26, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 5 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def A3: IdealEqSpanCertificate' Table ![![13, 0, 0], ![-4, 1, 0]] 
 ![![13, 0, 0], ![9, 1, 0], ![2, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![-4, 1, 0], ![2, -5, 4], ![152, -26, -2]]]
  hmulB := by decide  
  f := ![![![-27, 88, -72], ![26, 234, 0]], ![![-19, 59, -48], ![14, 156, 0]], ![![-2, 13, -11], ![11, 36, 0]]]
  g := ![![![1, 0, 0], ![-9, 13, 0], ![-2, 0, 13]], ![![-1, 1, 0], ![3, -5, 4], ![30, -26, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N3 : Nat.card (O ⧸ I3) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)

def Log00Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] ![114822808316477, -34061766327500, 7968395209052] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![60982113657159, -34061766327500, 7968395209052]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![114822808316479, -34061766327500, 7968395209052]
 hxeq :=  rfl
 m := 2
 C := ![114822808316477, -34061766327500, 7968395209052]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] ![-3, 0, 0] where
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
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] ![-123, -3, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-39, -3, -4]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-122, -3, -4]
 hxeq :=  rfl
 m := 1
 C := ![-123, -3, -4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log03Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![2, 1, 0], ![0, 0, 1]] ![6663722, -429182, -637843] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![2507362, -429182, -637843]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![6663723, -429182, -637843]
 hxeq :=  rfl
 m := 1
 C := ![6663722, -429182, -637843]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log03Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] ![114822808316477, -34061766327500, 7968395209052] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![45599058040211, -34061766327500, 7968395209052]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![114822808316479, -34061766327500, 7968395209052]
 hxeq :=  rfl
 m := 2
 C := ![114822808316477, -34061766327500, 7968395209052]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] ![-7, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
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
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] ![-123, -3, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-15, -3, -4]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-122, -3, -4]
 hxeq :=  rfl
 m := 1
 C := ![-123, -3, -4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log13Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![6, 1, 0], ![0, 0, 1]] ![6663718, -429182, -637843] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![1319830, -429182, -637843]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![6663723, -429182, -637843]
 hxeq :=  rfl
 m := 5
 C := ![6663718, -429182, -637843]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log13Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] ![114822808316478, -34061766327500, 7968395209052] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![37026905292554, -34061766327500, 7968395209052]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![114822808316479, -34061766327500, 7968395209052]
 hxeq :=  rfl
 m := 1
 C := ![114822808316478, -34061766327500, 7968395209052]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] ![-5, 0, 0] where
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
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] ![-125, -3, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-20, -3, -4]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-122, -3, -4]
 hxeq :=  rfl
 m := 3
 C := ![-125, -3, -4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log23Mem : IdealMemCertificate B I2
 ![![5, 0, 0], ![3, 1, 0], ![4, 0, 1]] ![6663722, -429182, -637843] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![2100528, -429182, -637843]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![6663723, -429182, -637843]
 hxeq :=  rfl
 m := 1
 C := ![6663722, -429182, -637843]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log23Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log30Mem : IdealMemCertificate B I3
 ![![13, 0, 0], ![9, 1, 0], ![2, 0, 1]] ![114822808316468, -34061766327500, 7968395209052] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![31187839603528, -34061766327500, 7968395209052]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![114822808316479, -34061766327500, 7968395209052]
 hxeq :=  rfl
 m := 11
 C := ![114822808316468, -34061766327500, 7968395209052]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log30Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log31Mem : IdealMemCertificate B I3
 ![![13, 0, 0], ![9, 1, 0], ![2, 0, 1]] ![-13, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 0, 0]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 12
 C := ![-13, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log31Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log32Mem : IdealMemCertificate B I3
 ![![13, 0, 0], ![9, 1, 0], ![2, 0, 1]] ![-126, -3, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-7, -3, -4]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-122, -3, -4]
 hxeq :=  rfl
 m := 4
 C := ![-126, -3, -4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log32Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log33Mem : IdealMemCertificate B I3
 ![![13, 0, 0], ![9, 1, 0], ![2, 0, 1]] ![6663713, -429182, -637843] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![907849, -429182, -637843]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![6663723, -429182, -637843]
 hxeq :=  rfl
 m := 10
 C := ![6663713, -429182, -637843]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log33Mem
 k := 10
 hpow := by zmod_pow
 heql := by decide

end Sat2
