import IdealArithmetic.Examples.NF5_1_48600000_1.ClassGroupData5_1_48600000_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_48600000_1.RI5_1_48600000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq11 : Fact $ Nat.Prime 11 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![1, 1, 0, 0, 0], ![0, 2, 2, 0, 0], ![0, 0, 0, 1, 0], ![4, 0, 2, 5, 8], ![4, 1, 3, -3, -3]]]
  hmulB := by decide  
  f := ![![![144, 63, 40, 0, 160], ![-693, 0, 1100, -220, 0]], ![![14, 6, 4, 0, 16], ![-65, 0, 110, -22, 0]], ![![130, 58, 37, 0, 144], ![-628, -5, 990, -198, 0]], ![![0, 0, 0, 0, 0], ![0, 0, 1, 0, 0]], ![![118, 51, 32, 0, 131], ![-569, 4, 900, -180, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 11, 0, 0, 0], ![-10, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![-9, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-2, 2, 2, 0, 0], ![0, 0, 0, 1, 0], ![-8, 0, 2, 5, 8], ![0, 1, 3, -3, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![6, 1, 0, 0, 0], ![0, 7, 2, 0, 0], ![0, 0, 5, 1, 0], ![4, 0, 2, 10, 8], ![4, 1, 3, -3, 2]]]
  hmulB := by decide  
  f := ![![![65, -20, 405, 121, 32], ![-88, 44, -891, -44, 0]], ![![58, -21, 405, 121, 32], ![-76, 44, -891, -44, 0]], ![![31, -7, 181, 56, 16], ![-42, 17, -396, -22, 0]], ![![26, -13, 204, 61, 16], ![-32, 25, -450, -22, 0]], ![![-5, -10, 35, 11, 3], ![12, 14, -81, -4, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-6, 11, 0, 0, 0], ![-1, 0, 11, 0, 0], ![-6, 0, 0, 11, 0], ![-1, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-4, 7, 2, 0, 0], ![-1, 0, 5, 1, 0], ![-6, 0, 2, 10, 8], ![1, 1, 3, -3, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![3, 1, 0, 0, 0], ![0, 4, 2, 0, 0], ![0, 0, 2, 1, 0], ![4, 0, 2, 7, 8], ![4, 1, 3, -3, -1]]]
  hmulB := by decide  
  f := ![![![6282, 1971, 15144, 7750, 208], ![-63829, 682, -234608, -806, 0]], ![![958, 298, 2336, 1196, 32], ![-9733, 124, -36208, -124, 0]], ![![5312, 1663, 12805, 6554, 176], ![-53973, 605, -198400, -682, 0]], ![![2416, 756, 5824, 2981, 80], ![-24548, 278, -90240, -310, 0]], ![![1416, 441, 3418, 1750, 47], ![-14387, 179, -52976, -182, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-3, 31, 0, 0, 0], ![-25, 0, 31, 0, 0], ![-12, 0, 0, 31, 0], ![-7, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![-2, 4, 2, 0, 0], ![-2, 0, 2, 1, 0], ![-6, 0, 2, 7, 8], ![-1, 1, 3, -3, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![11, 12, -5, -5, -8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![11, 12, -5, -5, -8]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![15, 12, -5, -5, -8]
 hxeq :=  rfl
 m := 4
 C := ![11, 12, -5, -5, -8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![-26997, -99902, 36483, 33365, 61972] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-77243, -99902, 36483, 33365, 61972]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-26991, -99902, 36483, 33365, 61972]
 hxeq :=  rfl
 m := 6
 C := ![-26997, -99902, 36483, 33365, 61972]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![10, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![655, 471, 553, 230, 264] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-702, 471, 553, 230, 264]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![658, 471, 553, 230, 264]
 hxeq :=  rfl
 m := 3
 C := ![655, 471, 553, 230, 264]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![7, 12, -5, -5, -8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-2, 12, -5, -5, -8]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![15, 12, -5, -5, -8]
 hxeq :=  rfl
 m := 8
 C := ![7, 12, -5, -5, -8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![-26999, -99902, 36483, 33365, 61972] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![24888, -99902, 36483, 33365, 61972]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-26991, -99902, 36483, 33365, 61972]
 hxeq :=  rfl
 m := 8
 C := ![-26999, -99902, 36483, 33365, 61972]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![11, 0, 0, 0, 0], ![6, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![6, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![656, 471, 553, 230, 264] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-397, 471, 553, 230, 264]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![658, 471, 553, 230, 264]
 hxeq :=  rfl
 m := 2
 C := ![656, 471, 553, 230, 264]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![12, 12, -5, -5, -8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![7, 12, -5, -5, -8]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![15, 12, -5, -5, -8]
 hxeq :=  rfl
 m := 3
 C := ![12, 12, -5, -5, -8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![-27001, -99902, 36483, 33365, 61972] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-47534, -99902, 36483, 33365, 61972]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-26991, -99902, 36483, 33365, 61972]
 hxeq :=  rfl
 m := 10
 C := ![-27001, -99902, 36483, 33365, 61972]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 14
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![31, 0, 0, 0, 0], ![3, 1, 0, 0, 0], ![25, 0, 1, 0, 0], ![12, 0, 0, 1, 0], ![7, 0, 0, 0, 1]] ![657, 471, 553, 230, 264] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-619, 471, 553, 230, 264]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![658, 471, 553, 230, 264]
 hxeq :=  rfl
 m := 1
 C := ![657, 471, 553, 230, 264]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

end Sat5
