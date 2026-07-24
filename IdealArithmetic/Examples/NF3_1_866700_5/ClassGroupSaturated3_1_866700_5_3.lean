import IdealArithmetic.Examples.NF3_1_866700_5.ClassGroupData3_1_866700_5
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_866700_5.RI3_1_866700_5

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq43 : Fact $ Nat.Prime 43 := {out := by norm_num}
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

def R43 : IsOrderOf (3 : ZMod 43) 42 where
 m := 3
 P := ![2, 3, 7]
 e := ![1, 1, 1]
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

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![11, -3, -3]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![-6, 1, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![-31, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![11, -3, -3]] 
 ![![13, 0, 0], ![6, 1, 0], ![12, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![11, -3, -3], ![-528, -7, -21], ![-42, -42, 11]]]
  hmulB := by decide  
  f := ![![![12937, 2512, 3072], ![9672, 520, 0]], ![![5844, 1136, 1389], ![4374, 235, 0]], ![![11941, 2319, 2836], ![8929, 480, 0]]]
  g := ![![![1, 0, 0], ![-6, 13, 0], ![-12, 0, 13]], ![![5, -3, -3], ![-18, -7, -21], ![6, -42, 11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![31, 0, 0], ![-6, 1, 0]] 
 ![![31, 0, 0], ![25, 1, 0], ![21, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![-6, 1, 0], ![-6, 0, 13], ![182, 0, -12]]]
  hmulB := by decide  
  f := ![![![-863, -6, 1950], ![186, -4650, 0]], ![![-689, -5, 1560], ![156, -3720, 0]], ![![-585, -4, 1321], ![124, -3150, 0]]]
  g := ![![![1, 0, 0], ![-25, 31, 0], ![-21, 0, 31]], ![![-1, 1, 0], ![-9, 0, 13], ![14, 0, -12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![43, 0, 0], ![-31, 1, 0]] 
 ![![43, 0, 0], ![12, 1, 0], ![16, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![-31, 1, 0], ![-6, -25, 13], ![182, 0, -37]]]
  hmulB := by decide  
  f := ![![![2234, 13079, -6786], ![-1247, 22446, 0]], ![![623, 3633, -1885], ![-343, 6235, 0]], ![![850, 4866, -2525], ![-438, 8352, 0]]]
  g := ![![![1, 0, 0], ![-12, 43, 0], ![-16, 0, 43]], ![![-1, 1, 0], ![2, -25, 13], ![18, 0, -37]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 43 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![13, 0, 0], ![6, 1, 0], ![12, 0, 1]] ![-37, 61, -91] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![53, 61, -91]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-27, 61, -91]
 hxeq :=  rfl
 m := 10
 C := ![-37, 61, -91]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 10
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![13, 0, 0], ![6, 1, 0], ![12, 0, 1]] ![-172, -20, -13] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![8, -20, -13]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-161, -20, -13]
 hxeq :=  rfl
 m := 11
 C := ![-172, -20, -13]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![13, 0, 0], ![6, 1, 0], ![12, 0, 1]] ![-98, -11, -7] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![4, -11, -7]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-89, -11, -7]
 hxeq :=  rfl
 m := 9
 C := ![-98, -11, -7]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![31, 0, 0], ![25, 1, 0], ![21, 0, 1]] ![-45, 61, -91] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![11, 61, -91]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-27, 61, -91]
 hxeq :=  rfl
 m := 18
 C := ![-45, 61, -91]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 26
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![31, 0, 0], ![25, 1, 0], ![21, 0, 1]] ![-184, -20, -13] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![19, -20, -13]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-161, -20, -13]
 hxeq :=  rfl
 m := 23
 C := ![-184, -20, -13]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 27
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![31, 0, 0], ![25, 1, 0], ![21, 0, 1]] ![-112, -11, -7] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![10, -11, -7]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-89, -11, -7]
 hxeq :=  rfl
 m := 23
 C := ![-112, -11, -7]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 27
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![43, 0, 0], ![12, 1, 0], ![16, 0, 1]] ![-36, 61, -91] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![16, 61, -91]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-27, 61, -91]
 hxeq :=  rfl
 m := 9
 C := ![-36, 61, -91]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![43, 0, 0], ![12, 1, 0], ![16, 0, 1]] ![-190, -20, -13] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![6, -20, -13]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-161, -20, -13]
 hxeq :=  rfl
 m := 29
 C := ![-190, -20, -13]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 41
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![43, 0, 0], ![12, 1, 0], ![16, 0, 1]] ![-115, -11, -7] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![3, -11, -7]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 alpha1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-89, -11, -7]
 hxeq :=  rfl
 m := 26
 C := ![-115, -11, -7]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 17
 hpow := by zmod_pow
 heql := by decide

end Sat3
