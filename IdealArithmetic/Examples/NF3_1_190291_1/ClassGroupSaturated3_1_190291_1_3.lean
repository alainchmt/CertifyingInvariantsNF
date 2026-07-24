import IdealArithmetic.Examples.NF3_1_190291_1.ClassGroupData3_1_190291_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_190291_1.RI3_1_190291_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq43 : Fact $ Nat.Prime 43 := {out := by norm_num}
instance hq19 : Fact $ Nat.Prime 19 := {out := by norm_num}
instance hq37 : Fact $ Nat.Prime 37 := {out := by norm_num}

def R43 : IsOrderOf (3 : ZMod 43) 42 where
 m := 3
 P := ![2, 3, 7]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R19 : IsOrderOf (2 : ZMod 19) 18 where
 m := 2
 P := ![2, 3]
 e := ![1, 2]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-6, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![0, 1, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![12, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-6, 1, 0]] 
 ![![19, 0, 0], ![13, 1, 0], ![6, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-6, 1, 0], ![2, -5, 8], ![83, -5, -7]]]
  hmulB := by decide  
  f := ![![![-35, 104, -168], ![19, 399, 0]], ![![-21, 69, -112], ![20, 266, 0]], ![![-6, 32, -53], ![22, 126, 0]]]
  g := ![![![1, 0, 0], ![-13, 19, 0], ![-6, 0, 19]], ![![-1, 1, 0], ![1, -5, 8], ![10, -5, -7]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 19 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![0, 1, 0]] 
 ![![37, 0, 0], ![0, 1, 0], ![28, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![0, 1, 0], ![2, 1, 8], ![83, -5, -1]]]
  hmulB := by decide  
  f := ![![![-37, -19, -152], ![0, 703, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-28, -15, -115], ![23, 532, 0]]]
  g := ![![![1, 0, 0], ![0, 37, 0], ![-28, 0, 37]], ![![0, 1, 0], ![-6, 1, 8], ![3, -5, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 37 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![12, 1, 0]] 
 ![![43, 0, 0], ![12, 1, 0], ![13, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![12, 1, 0], ![2, 13, 8], ![83, -5, 11]]]
  hmulB := by decide  
  f := ![![![-479, -3505, -2160], ![-215, 11610, 0]], ![![-138, -974, -600], ![-42, 3225, 0]], ![![-149, -1060, -653], ![-50, 3510, 0]]]
  g := ![![![1, 0, 0], ![-12, 43, 0], ![-13, 0, 43]], ![![0, 1, 0], ![-6, 13, 8], ![0, -5, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 43 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![19, 0, 0], ![13, 1, 0], ![6, 0, 1]] ![-29, 5, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-4, 5, -3]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-20, 5, -3]
 hxeq :=  rfl
 m := 9
 C := ![-29, 5, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![19, 0, 0], ![13, 1, 0], ![6, 0, 1]] ![-19, -1, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, -1, -1]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-11, -1, -1]
 hxeq :=  rfl
 m := 8
 C := ![-19, -1, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![19, 0, 0], ![13, 1, 0], ![6, 0, 1]] ![-38, -2, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, -2, -2]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-23, -2, -2]
 hxeq :=  rfl
 m := 15
 C := ![-38, -2, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 11
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![37, 0, 0], ![0, 1, 0], ![28, 0, 1]] ![-47, 5, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![1, 5, -3]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-20, 5, -3]
 hxeq :=  rfl
 m := 27
 C := ![-47, 5, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![37, 0, 0], ![0, 1, 0], ![28, 0, 1]] ![-28, -1, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, -1, -1]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-11, -1, -1]
 hxeq :=  rfl
 m := 17
 C := ![-28, -1, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![37, 0, 0], ![0, 1, 0], ![28, 0, 1]] ![-56, -2, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, -2, -2]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-23, -2, -2]
 hxeq :=  rfl
 m := 33
 C := ![-56, -2, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 20
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![43, 0, 0], ![12, 1, 0], ![13, 0, 1]] ![-22, 5, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 5, -3]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-20, 5, -3]
 hxeq :=  rfl
 m := 2
 C := ![-22, 5, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 27
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![43, 0, 0], ![12, 1, 0], ![13, 0, 1]] ![-25, -1, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![0, -1, -1]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-11, -1, -1]
 hxeq :=  rfl
 m := 14
 C := ![-25, -1, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 20
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![43, 0, 0], ![12, 1, 0], ![13, 0, 1]] ![-50, -2, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![0, -2, -2]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-23, -2, -2]
 hxeq :=  rfl
 m := 27
 C := ![-50, -2, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

end Sat3
