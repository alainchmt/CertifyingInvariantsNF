import IdealArithmetic.Examples.NF3_1_193320_1.ClassGroupData3_1_193320_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_193320_1.RI3_1_193320_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq11 : Fact $ Nat.Prime 11 := {out := by norm_num}

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![4, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![11, 0, 0], ![4, 1, 0]] 
 ![![11, 0, 0], ![4, 1, 0], ![6, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![4, 1, 0], ![0, 4, 1], ![186, 57, 4]]]
  hmulB := by decide  
  f := ![![![5, 1, 0], ![-11, 0, 0]], ![![-4, -1, 0], ![12, 0, 0]], ![![2, 0, 0], ![-4, 1, 0]]]
  g := ![![![1, 0, 0], ![-4, 11, 0], ![-6, 0, 11]], ![![0, 1, 0], ![-2, 4, 1], ![-6, 57, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![11, 0, 0], ![-3, 1, 0]] 
 ![![11, 0, 0], ![8, 1, 0], ![2, 0, 1]] where
  M :=![![![11, 0, 0], ![0, 11, 0], ![0, 0, 11]], ![![-3, 1, 0], ![0, -3, 1], ![186, 57, -3]]]
  hmulB := by decide  
  f := ![![![19, -6, 0], ![66, 0, 0]], ![![16, -5, 0], ![56, 0, 0]], ![![4, -1, 0], ![14, 1, 0]]]
  g := ![![![1, 0, 0], ![-8, 11, 0], ![-2, 0, 11]], ![![-1, 1, 0], ![2, -3, 1], ![-24, 57, -3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![11, 0, 0], ![4, 1, 0], ![6, 0, 1]] ![-395757028, -198076481, 27490455] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![21055106, -198076481, 27490455]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-395757025, -198076481, 27490455]
 hxeq :=  rfl
 m := 3
 C := ![-395757028, -198076481, 27490455]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![11, 0, 0], ![4, 1, 0], ![6, 0, 1]] ![1914, 804, 91] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-168, 804, 91]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1916, 804, 91]
 hxeq :=  rfl
 m := 2
 C := ![1914, 804, 91]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![11, 0, 0], ![8, 1, 0], ![2, 0, 1]] ![-395757032, -198076481, 27490455] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![103079446, -198076481, 27490455]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-395757025, -198076481, 27490455]
 hxeq :=  rfl
 m := 7
 C := ![-395757032, -198076481, 27490455]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![11, 0, 0], ![8, 1, 0], ![2, 0, 1]] ![1906, 804, 91] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-428, 804, 91]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1916, 804, 91]
 hxeq :=  rfl
 m := 10
 C := ![1906, 804, 91]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

end Sat5
