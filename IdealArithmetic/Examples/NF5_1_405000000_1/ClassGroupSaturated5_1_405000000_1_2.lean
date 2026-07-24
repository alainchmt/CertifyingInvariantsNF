import IdealArithmetic.Examples.NF5_1_405000000_1.ClassGroupData5_1_405000000_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_405000000_1.RI5_1_405000000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat2 
instance hq11 : Fact $ Nat.Prime 11 := {out := by norm_num}
instance hq3 : Fact $ Nat.Prime 3 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
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

def R7 : IsOrderOf (3 : ZMod 7) 6 where
 m := 2
 P := ![2, 3]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![0, 1, 0, 0, 4], ![60, -2, 6, -4, 0]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, -1, 0, -1, 0], ![1, 0, 2, 0, 0]], ![![0, 0, 0, 0, 3], ![2, 0, 0, -2, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 1, 0, 2, 0], ![0, 1, 0, 0, 4], ![20, -2, 6, -4, 0]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![0, 1, 0, 1, 4], ![60, -2, 6, -4, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, 3, 0, -8], ![3, -6, -3, 6, 0]], ![![0, 0, 1, -1, -4], ![1, -3, 0, 3, 0]], ![![0, 0, 2, -1, -4], ![2, -5, 0, 3, 0]], ![![0, -1, -1, -1, 0], ![0, 1, 2, 0, 0]], ![![0, 0, 2, 0, -5], ![2, -4, -2, 4, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![-3, 1, 0, 1, 4], ![16, -2, 6, -4, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 1, 1, 2, 0], ![0, 1, 0, 1, 4], ![60, -2, 6, -4, 1]]]
  hmulB := by decide  
  f := ![![![0, 16, 23, 42, -24], ![7, 7, -168, 42, 0]], ![![0, 2, 3, 7, -4], ![1, 7, -28, 7, 0]], ![![0, 13, 19, 35, -20], ![6, 8, -140, 35, 0]], ![![0, -1, -1, -1, 0], ![0, 3, 4, 0, 0]], ![![0, 11, 16, 30, -17], ![5, 8, -120, 30, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 7, 0, 0, 0], ![-6, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![-5, 0, 0, 0, 7]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-1, 1, 1, 2, 0], ![-3, 1, 0, 1, 4], ![3, -2, 6, -4, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def A3: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 1, -4, 2, 0], ![0, 1, 0, -4, 4], ![60, -2, 6, -4, -4]]]
  hmulB := by decide  
  f := ![![![1045, -1489, 6227, -3080, -80], ![2871, 1023, 17380, 220, 0]], ![![777, -1113, 4651, -2300, -60], ![2135, 759, 12980, 165, 0]], ![![786, -1121, 4690, -2320, -60], ![2160, 771, 13090, 165, 0]], ![![261, -372, 1555, -769, -20], ![717, 255, 4340, 55, 0]], ![![380, -540, 2264, -1120, -29], ![1044, 376, 6320, 80, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-7, 11, 0, 0, 0], ![-6, 0, 11, 0, 0], ![-3, 0, 0, 11, 0], ![-4, 0, 0, 0, 11]], ![![-1, 1, 0, 0, 0], ![2, -4, 1, 0, 0], ![1, 1, -4, 2, 0], ![-1, 1, 0, -4, 4], ![6, -2, 6, -4, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N3 : Nat.card (O ⧸ I3) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)

def Log00Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-6170728365, 1612948664, -343950842, 311415441, -68113181] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-2056909455, 1612948664, -343950842, 311415441, -68113181]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-6170728364, 1612948664, -343950842, 311415441, -68113181]
 hxeq :=  rfl
 m := 1
 C := ![-6170728365, 1612948664, -343950842, 311415441, -68113181]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![61616422629, -17026004959, 3671410855, -4004626858, 1814584410] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![20538807543, -17026004959, 3671410855, -4004626858, 1814584410]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![61616422631, -17026004959, 3671410855, -4004626858, 1814584410]
 hxeq :=  rfl
 m := 2
 C := ![61616422629, -17026004959, 3671410855, -4004626858, 1814584410]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-3, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log03Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-288, -96, -56, -14, -16] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-96, -96, -56, -14, -16]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-286, -96, -56, -14, -16]
 hxeq :=  rfl
 m := 2
 C := ![-288, -96, -56, -14, -16]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log03Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-6170728365, 1612948664, -343950842, 311415441, -68113181] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-2319849661, 1612948664, -343950842, 311415441, -68113181]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-6170728364, 1612948664, -343950842, 311415441, -68113181]
 hxeq :=  rfl
 m := 1
 C := ![-6170728365, 1612948664, -343950842, 311415441, -68113181]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![61616422630, -17026004959, 3671410855, -4004626858, 1814584410] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![22556812353, -17026004959, 3671410855, -4004626858, 1814584410]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![61616422631, -17026004959, 3671410855, -4004626858, 1814584410]
 hxeq :=  rfl
 m := 1
 C := ![61616422630, -17026004959, 3671410855, -4004626858, 1814584410]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-3, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log13Mem : IdealMemCertificate B I1
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-288, -96, -56, -14, -16] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-16, -96, -56, -14, -16]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-286, -96, -56, -14, -16]
 hxeq :=  rfl
 m := 2
 C := ![-288, -96, -56, -14, -16]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log13Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-6170728367, 1612948664, -343950842, 311415441, -68113181] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-768486582, 1612948664, -343950842, 311415441, -68113181]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-6170728364, 1612948664, -343950842, 311415441, -68113181]
 hxeq :=  rfl
 m := 3
 C := ![-6170728367, 1612948664, -343950842, 311415441, -68113181]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![61616422628, -17026004959, 3671410855, -4004626858, 1814584410] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![6791577201, -17026004959, 3671410855, -4004626858, 1814584410]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![61616422631, -17026004959, 3671410855, -4004626858, 1814584410]
 hxeq :=  rfl
 m := 3
 C := ![61616422628, -17026004959, 3671410855, -4004626858, 1814584410]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-7, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 6
 C := ![-7, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log23Mem : IdealMemCertificate B I2
 ![![7, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-288, -96, -56, -14, -16] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![32, -96, -56, -14, -16]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-286, -96, -56, -14, -16]
 hxeq :=  rfl
 m := 2
 C := ![-288, -96, -56, -14, -16]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log23Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log30Mem : IdealMemCertificate B I3
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![-6170728373, 1612948664, -343950842, 311415441, -68113181] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1459950688, 1612948664, -343950842, 311415441, -68113181]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-6170728364, 1612948664, -343950842, 311415441, -68113181]
 hxeq :=  rfl
 m := 9
 C := ![-6170728373, 1612948664, -343950842, 311415441, -68113181]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log30Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log31Mem : IdealMemCertificate B I3
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![61616422623, -17026004959, 3671410855, -4004626858, 1814584410] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![14865957740, -17026004959, 3671410855, -4004626858, 1814584410]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![61616422631, -17026004959, 3671410855, -4004626858, 1814584410]
 hxeq :=  rfl
 m := 8
 C := ![61616422623, -17026004959, 3671410855, -4004626858, 1814584410]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log31Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log32Mem : IdealMemCertificate B I3
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![-11, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 10
 C := ![-11, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log32Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log33Mem : IdealMemCertificate B I3
 ![![11, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![6, 0, 1, 0, 0], ![3, 0, 0, 1, 0], ![4, 0, 0, 0, 1]] ![-289, -96, -56, -14, -16] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![75, -96, -56, -14, -16]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-286, -96, -56, -14, -16]
 hxeq :=  rfl
 m := 3
 C := ![-289, -96, -56, -14, -16]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log33Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

end Sat2
