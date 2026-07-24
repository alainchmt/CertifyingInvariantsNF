import IdealArithmetic.Examples.NF5_1_421875000_2.ClassGroupData5_1_421875000_2
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_421875000_2.RI5_1_421875000_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![-4, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-4, 1, 0, 0, 0], ![0, -4, 1, 0, 0], ![0, 1, -4, 2, 0], ![-6, 9, 7, 5, 24], ![6, -5, -3, -4, -13]]]
  hmulB := by decide  
  f := ![![![-4505, 1399, -355, 299, 360], ![-14352, 156, -1456, -195, 0]], ![![-4525, 1406, -363, 303, 360], ![-14416, 156, -1482, -195, 0]], ![![-4520, 1405, -363, 303, 360], ![-14400, 157, -1482, -195, 0]], ![![-2999, 932, -236, 199, 240], ![-9554, 106, -968, -130, 0]], ![![-3466, 1080, -274, 230, 277], ![-11042, 132, -1120, -150, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-9, 13, 0, 0, 0], ![-10, 0, 13, 0, 0], ![-9, 0, 0, 13, 0], ![-10, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0], ![2, -4, 1, 0, 0], ![1, 1, -4, 2, 0], ![-34, 9, 7, 5, 24], ![19, -5, -3, -4, -13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![13, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![13, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] where
  M :=![![![13, 0, 0, 0, 0], ![0, 13, 0, 0, 0], ![0, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![0, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![-6, 9, 7, 8, 24], ![6, -5, -3, -4, -10]]]
  hmulB := by decide  
  f := ![![![-915, -374, 1770, -3452, 1152], ![-8164, 6292, 24934, -624, 0]], ![![-915, -373, 1769, -3454, 1152], ![-8163, 6318, 24947, -624, 0]], ![![-840, -342, 1623, -3164, 1056], ![-7500, 5760, 22854, -572, 0]], ![![0, 0, 0, -1, 0], ![0, 7, 7, 0, 0]], ![![-561, -231, 1088, -2124, 709], ![-4997, 3886, 15342, -384, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-12, 13, 0, 0, 0], ![-12, 0, 13, 0, 0], ![0, 0, 0, 13, 0], ![-8, 0, 0, 0, 13]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![-30, 9, 7, 8, 24], ![14, -5, -3, -4, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-11, 1, 0, 0, 0], ![0, -11, 1, 0, 0], ![0, 1, -11, 2, 0], ![-6, 9, 7, -2, 24], ![6, -5, -3, -4, -20]]]
  hmulB := by decide  
  f := ![![![-1005238, 120068, -234869, 42222, 14976], ![-2822395, 4712, -673785, -19344, 0]], ![![-670162, 80053, -156580, 28148, 9984], ![-1881606, 3162, -449190, -12896, 0]], ![![-125666, 15013, -29393, 5284, 1872], ![-352831, 590, -84320, -2418, 0]], ![![-712042, 85048, -166364, 29907, 10608], ![-1999192, 3338, -477260, -13702, 0]], ![![-324254, 38739, -75765, 13620, 4831], ![-910404, 1545, -217350, -6240, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-20, 31, 0, 0, 0], ![-3, 0, 31, 0, 0], ![-22, 0, 0, 31, 0], ![-10, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![7, -11, 1, 0, 0], ![-1, 1, -11, 2, 0], ![-13, 9, 7, -2, 24], ![13, -5, -3, -4, -20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] ![-4169, -1618, -1024, -1218, -2658] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![4475, -1618, -1024, -1218, -2658]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4159, -1618, -1024, -1218, -2658]
 hxeq :=  rfl
 m := 10
 C := ![-4169, -1618, -1024, -1218, -2658]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 10
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] ![35154921739646228773, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![44005693057461709171, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![35154921739646228779, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980]
 hxeq :=  rfl
 m := 6
 C := ![35154921739646228773, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![13, 0, 0, 0, 0], ![9, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![9, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] ![-3, 0, -2, -3, -6] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![8, 0, -2, -3, -6]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, 0, -2, -3, -6]
 hxeq :=  rfl
 m := 4
 C := ![-3, 0, -2, -3, -6]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] ![-4166, -1618, -1024, -1218, -2658] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![3754, -1618, -1024, -1218, -2658]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4159, -1618, -1024, -1218, -2658]
 hxeq :=  rfl
 m := 7
 C := ![-4166, -1618, -1024, -1218, -2658]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 11
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] ![35154921739646228771, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![42655311727786072671, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![35154921739646228779, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980]
 hxeq :=  rfl
 m := 8
 C := ![35154921739646228771, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![13, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![12, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![8, 0, 0, 0, 1]] ![-7, 0, -2, -3, -6] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![5, 0, -2, -3, -6]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, 0, -2, -3, -6]
 hxeq :=  rfl
 m := 8
 C := ![-7, 0, -2, -3, -6]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] ![-4178, -1618, -1024, -1218, -2658] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![2730, -1618, -1024, -1218, -2658]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-4159, -1618, -1024, -1218, -2658]
 hxeq :=  rfl
 m := 19
 C := ![-4178, -1618, -1024, -1218, -2658]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] ![35154921739646228751, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![30179465316051560079, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![35154921739646228779, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980]
 hxeq :=  rfl
 m := 28
 C := ![35154921739646228751, -26694643017895333030, -3085950708910050646, -7034615139701371880, -20249625749988513980]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 16
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![10, 0, 0, 0, 1]] ![-8, 0, -2, -3, -6] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![4, 0, -2, -3, -6]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, 0, -2, -3, -6]
 hxeq :=  rfl
 m := 9
 C := ![-8, 0, -2, -3, -6]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

end Sat3
