import IdealArithmetic.Examples.NF3_3_587412_2.ClassGroupData3_3_587412_2
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_3_587412_2.RI3_3_587412_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq19 : Fact $ Nat.Prime 19 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}
instance hq37 : Fact $ Nat.Prime 37 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R19 : IsOrderOf (2 : ZMod 19) 18 where
 m := 2
 P := ![2, 3]
 e := ![1, 2]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R37 : IsOrderOf (2 : ZMod 37) 36 where
 m := 2
 P := ![2, 3]
 e := ![2, 2]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-4, 1, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![10, 1, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![12, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![0, 1, 0]] 
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 0, 1], ![1162, 210, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]
  g := ![![![1, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![0, 1, 0], ![0, 0, 1], ![166, 210, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-4, 1, 0]] 
 ![![19, 0, 0], ![15, 1, 0], ![3, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-4, 1, 0], ![0, -4, 1], ![1162, 210, -4]]]
  hmulB := by decide  
  f := ![![![29, -7, 0], ![133, 0, 0]], ![![25, -6, 0], ![115, 0, 0]], ![![5, -1, 0], ![23, 1, 0]]]
  g := ![![![1, 0, 0], ![-15, 19, 0], ![-3, 0, 19]], ![![-1, 1, 0], ![3, -4, 1], ![-104, 210, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 19 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![31, 0, 0], ![10, 1, 0]] 
 ![![31, 0, 0], ![10, 1, 0], ![24, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![10, 1, 0], ![0, 10, 1], ![1162, 210, 10]]]
  hmulB := by decide  
  f := ![![![121, 12, 0], ![-372, 0, 0]], ![![30, 3, 0], ![-92, 0, 0]], ![![84, 8, 0], ![-258, 1, 0]]]
  g := ![![![1, 0, 0], ![-10, 31, 0], ![-24, 0, 31]], ![![0, 1, 0], ![-4, 10, 1], ![-38, 210, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def A3: IdealEqSpanCertificate' Table ![![37, 0, 0], ![12, 1, 0]] 
 ![![37, 0, 0], ![12, 1, 0], ![4, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![12, 1, 0], ![0, 12, 1], ![1162, 210, 12]]]
  hmulB := by decide  
  f := ![![![169, 14, 0], ![-518, 0, 0]], ![![60, 5, 0], ![-184, 0, 0]], ![![4, 0, 0], ![-12, 1, 0]]]
  g := ![![![1, 0, 0], ![-12, 37, 0], ![-4, 0, 37]], ![![0, 1, 0], ![-4, 12, 1], ![-38, 210, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N3 : Nat.card (O ⧸ I3) = 37 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)

def Log00Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] ![-14, -1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-2, -1, 0]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-9, -1, 0]
 hxeq :=  rfl
 m := 5
 C := ![-14, -1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] ![-35, -4, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-5, -4, 0]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-31, -4, 0]
 hxeq :=  rfl
 m := 4
 C := ![-35, -4, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] ![-147, -8, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-21, -8, 1]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-145, -8, 1]
 hxeq :=  rfl
 m := 2
 C := ![-147, -8, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log03Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![0, 1, 0], ![0, 0, 1]] ![903, 46, -6] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![129, 46, -6]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![907, 46, -6]
 hxeq :=  rfl
 m := 4
 C := ![903, 46, -6]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log03Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![19, 0, 0], ![15, 1, 0], ![3, 0, 1]] ![-15, -1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, -1, 0]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-9, -1, 0]
 hxeq :=  rfl
 m := 6
 C := ![-15, -1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 14
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![19, 0, 0], ![15, 1, 0], ![3, 0, 1]] ![-41, -4, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![1, -4, 0]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-31, -4, 0]
 hxeq :=  rfl
 m := 10
 C := ![-41, -4, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 17
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![19, 0, 0], ![15, 1, 0], ![3, 0, 1]] ![-155, -8, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-2, -8, 1]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-145, -8, 1]
 hxeq :=  rfl
 m := 10
 C := ![-155, -8, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 17
 hpow := by zmod_pow
 heql := by decide

def Log13Mem : IdealMemCertificate B I1
 ![![19, 0, 0], ![15, 1, 0], ![3, 0, 1]] ![900, 46, -6] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![12, 46, -6]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![907, 46, -6]
 hxeq :=  rfl
 m := 7
 C := ![900, 46, -6]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log13Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![31, 0, 0], ![10, 1, 0], ![24, 0, 1]] ![-10, -1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![0, -1, 0]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-9, -1, 0]
 hxeq :=  rfl
 m := 1
 C := ![-10, -1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![31, 0, 0], ![10, 1, 0], ![24, 0, 1]] ![-40, -4, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![0, -4, 0]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-31, -4, 0]
 hxeq :=  rfl
 m := 9
 C := ![-40, -4, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![31, 0, 0], ![10, 1, 0], ![24, 0, 1]] ![-149, -8, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-3, -8, 1]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-145, -8, 1]
 hxeq :=  rfl
 m := 4
 C := ![-149, -8, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 18
 hpow := by zmod_pow
 heql := by decide

def Log23Mem : IdealMemCertificate B I2
 ![![31, 0, 0], ![10, 1, 0], ![24, 0, 1]] ![905, 46, -6] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![19, 46, -6]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![907, 46, -6]
 hxeq :=  rfl
 m := 2
 C := ![905, 46, -6]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log23Mem
 k := 24
 hpow := by zmod_pow
 heql := by decide

def Log30Mem : IdealMemCertificate B I3
 ![![37, 0, 0], ![12, 1, 0], ![4, 0, 1]] ![-12, -1, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![0, -1, 0]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-9, -1, 0]
 hxeq :=  rfl
 m := 3
 C := ![-12, -1, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log30Mem
 k := 26
 hpow := by zmod_pow
 heql := by decide

def Log31Mem : IdealMemCertificate B I3
 ![![37, 0, 0], ![12, 1, 0], ![4, 0, 1]] ![-48, -4, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![0, -4, 0]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-31, -4, 0]
 hxeq :=  rfl
 m := 17
 C := ![-48, -4, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log31Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log32Mem : IdealMemCertificate B I3
 ![![37, 0, 0], ![12, 1, 0], ![4, 0, 1]] ![-166, -8, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-2, -8, 1]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-145, -8, 1]
 hxeq :=  rfl
 m := 21
 C := ![-166, -8, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log32Mem
 k := 22
 hpow := by zmod_pow
 heql := by decide

def Log33Mem : IdealMemCertificate B I3
 ![![37, 0, 0], ![12, 1, 0], ![4, 0, 1]] ![898, 46, -6] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![10, 46, -6]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![907, 46, -6]
 hxeq :=  rfl
 m := 9
 C := ![898, 46, -6]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log33Mem
 k := 16
 hpow := by zmod_pow
 heql := by decide

end Sat3
