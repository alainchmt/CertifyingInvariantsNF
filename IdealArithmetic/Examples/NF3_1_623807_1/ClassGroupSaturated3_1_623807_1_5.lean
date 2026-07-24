import IdealArithmetic.Examples.NF3_1_623807_1.ClassGroupData3_1_623807_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_623807_1.RI3_1_623807_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq41 : Fact $ Nat.Prime 41 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

def R41 : IsOrderOf (6 : ZMod 41) 40 where
 m := 2
 P := ![2, 5]
 e := ![3, 1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![2, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![14, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![2, 1, 0]] 
 ![![31, 0, 0], ![2, 1, 0], ![28, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![2, 1, 0], ![0, 3, 2], ![152, 0, 1]]]
  hmulB := by decide  
  f := ![![![25, 12, 0], ![-372, 0, 0]], ![![-2, -1, 0], ![32, 0, 0]], ![![24, 10, -1], ![-358, 16, 0]]]
  g := ![![![1, 0, 0], ![-2, 31, 0], ![-28, 0, 31]], ![![0, 1, 0], ![-2, 3, 2], ![4, 0, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![41, 0, 0], ![14, 1, 0]] 
 ![![41, 0, 0], ![14, 1, 0], ![18, 0, 1]] where
  M :=![![![41, 0, 0], ![0, 41, 0], ![0, 0, 41]], ![![14, 1, 0], ![0, 15, 2], ![152, 0, 13]]]
  hmulB := by decide  
  f := ![![![15, 1, 0], ![-41, 0, 0]], ![![-14, -1, 0], ![42, 0, 0]], ![![10, -7, -1], ![-28, 21, 0]]]
  g := ![![![1, 0, 0], ![-14, 41, 0], ![-18, 0, 41]], ![![0, 1, 0], ![-6, 15, 2], ![-2, 0, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 41 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![31, 0, 0], ![2, 1, 0], ![28, 0, 1]] ![18053076206431471, -82494427526000, -894686488587598] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![1395783443288265, -82494427526000, -894686488587598]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![18053076206431487, -82494427526000, -894686488587598]
 hxeq :=  rfl
 m := 16
 C := ![18053076206431471, -82494427526000, -894686488587598]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![31, 0, 0], ![2, 1, 0], ![28, 0, 1]] ![-36, -4, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, -4, -1]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-23, -4, -1]
 hxeq :=  rfl
 m := 13
 C := ![-36, -4, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 11
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![41, 0, 0], ![14, 1, 0], ![18, 0, 1]] ![18053076206431484, -82494427526000, -894686488587598] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![861276950887128, -82494427526000, -894686488587598]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![18053076206431487, -82494427526000, -894686488587598]
 hxeq :=  rfl
 m := 3
 C := ![18053076206431484, -82494427526000, -894686488587598]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 15
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![41, 0, 0], ![14, 1, 0], ![18, 0, 1]] ![-33, -4, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![1, -4, -1]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R41) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 3 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-23, -4, -1]
 hxeq :=  rfl
 m := 10
 C := ![-33, -4, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

end Sat5
