import IdealArithmetic.Examples.NF3_1_760455_3.ClassGroupData3_1_760455_3
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_760455_3.RI3_1_760455_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R7 : IsOrderOf (3 : ZMod 7) 6 where
 m := 2
 P := ![2, 3]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-37, -3, -2]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![2, 1, 0]] 
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![2, 1, 7], ![37, -30, 3]]]
  hmulB := by decide  
  f := ![![![283, -247, 24], ![49, 0, -56]], ![![70, -62, 6], ![15, 0, -14]], ![![80, -71, 7], ![17, 0, -16]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![-2, 0, 7]], ![![0, 1, 0], ![-2, 1, 7], ![13, -30, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-37, -3, -2]] 
 ![![7, 0, 0], ![6, 1, 0], ![6, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-37, -3, -2], ![-80, 26, -23], ![-115, 88, 20]]]
  hmulB := by decide  
  f := ![![![31, -160, 95], ![-70, 35, 0]], ![![31, -132, 79], ![-57, 29, 0]], ![![53, -135, 83], ![-55, 30, 0]]]
  g := ![![![1, 0, 0], ![-6, 7, 0], ![-6, 0, 7]], ![![-1, -3, -2], ![-14, 26, -23], ![-109, 88, 20]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] ![196502436, -153965161, -62777783] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![89998332, -153965161, -62777783]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![196502439, -153965161, -62777783]
 hxeq :=  rfl
 m := 3
 C := ![196502436, -153965161, -62777783]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] ![-30, 0, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-4, 0, -1]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-28, 0, -1]
 hxeq :=  rfl
 m := 2
 C := ![-30, 0, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![6, 1, 0], ![6, 0, 1]] ![196502437, -153965161, -62777783] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![213851443, -153965161, -62777783]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![196502439, -153965161, -62777783]
 hxeq :=  rfl
 m := 2
 C := ![196502437, -153965161, -62777783]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![6, 1, 0], ![6, 0, 1]] ![-34, 0, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-4, 0, -1]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-28, 0, -1]
 hxeq :=  rfl
 m := 6
 C := ![-34, 0, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

end Sat3
