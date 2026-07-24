import IdealArithmetic.Examples.NF3_1_680884_1.ClassGroupData3_1_680884_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_680884_1.RI3_1_680884_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat7 
instance hq43 : Fact $ Nat.Prime 43 := {out := by norm_num}
instance hq127 : Fact $ Nat.Prime 127 := {out := by norm_num}

def R43 : IsOrderOf (3 : ZMod 43) 42 where
 m := 3
 P := ![2, 3, 7]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R127 : IsOrderOf (3 : ZMod 127) 126 where
 m := 3
 P := ![2, 3, 7]
 e := ![1, 2, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0], ![12, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![127, 0, 0], ![-12, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![43, 0, 0], ![12, 1, 0]] 
 ![![43, 0, 0], ![12, 1, 0], ![36, 0, 1]] where
  M :=![![![43, 0, 0], ![0, 43, 0], ![0, 0, 43]], ![![12, 1, 0], ![1, 12, 2], ![355, 73, 13]]]
  hmulB := by decide  
  f := ![![![-563, -7769, -1296], ![-301, 27864, 0]], ![![-156, -2158, -360], ![-85, 7740, 0]], ![![-468, -6504, -1085], ![-264, 23328, 0]]]
  g := ![![![1, 0, 0], ![-12, 43, 0], ![-36, 0, 43]], ![![0, 1, 0], ![-5, 12, 2], ![-23, 73, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 43 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![127, 0, 0], ![-12, 1, 0]] 
 ![![127, 0, 0], ![115, 1, 0], ![119, 0, 1]] where
  M :=![![![127, 0, 0], ![0, 127, 0], ![0, 0, 127]], ![![-12, 1, 0], ![1, -12, 2], ![355, 73, -11]]]
  hmulB := by decide  
  f := ![![![-6971, 85237, -14208], ![1397, 902208, 0]], ![![-6311, 77174, -12864], ![1271, 816864, 0]], ![![-6535, 79868, -13313], ![1276, 845376, 0]]]
  g := ![![![1, 0, 0], ![-115, 127, 0], ![-119, 0, 127]], ![![-1, 1, 0], ![9, -12, 2], ![-53, 73, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 127 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![43, 0, 0], ![12, 1, 0], ![36, 0, 1]] ![1090, -366, 40] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![94, -366, 40]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 7 zeta1 6 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1121, -366, 40]
 hxeq :=  rfl
 m := 31
 C := ![1090, -366, 40]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 34
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![43, 0, 0], ![12, 1, 0], ![36, 0, 1]] ![-456013475, -124014976, -18465152] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![39463063, -124014976, -18465152]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 7 alpha0 4 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-456013440, -124014976, -18465152]
 hxeq :=  rfl
 m := 35
 C := ![-456013475, -124014976, -18465152]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 18
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![127, 0, 0], ![115, 1, 0], ![119, 0, 1]] ![1024, -366, 40] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![302, -366, 40]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R127) ▸ IsPrimitiveRoot.orderOf _) 7 zeta1 6 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1121, -366, 40]
 hxeq :=  rfl
 m := 97
 C := ![1024, -366, 40]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 97
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![127, 0, 0], ![115, 1, 0], ![119, 0, 1]] ![-456013481, -124014976, -18465152] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![126008361, -124014976, -18465152]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R127) ▸ IsPrimitiveRoot.orderOf _) 7 alpha0 3 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-456013440, -124014976, -18465152]
 hxeq :=  rfl
 m := 41
 C := ![-456013481, -124014976, -18465152]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 80
 hpow := by zmod_pow
 heql := by decide

end Sat7
