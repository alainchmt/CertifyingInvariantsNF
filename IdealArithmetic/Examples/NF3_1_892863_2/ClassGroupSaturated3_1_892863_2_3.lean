import IdealArithmetic.Examples.NF3_1_892863_2.ClassGroupData3_1_892863_2
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_892863_2.RI3_1_892863_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq19 : Fact $ Nat.Prime 19 := {out := by norm_num}
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}

def R19 : IsOrderOf (2 : ZMod 19) 18 where
 m := 2
 P := ![2, 3]
 e := ![1, 2]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![0, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-13, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![0, 1, 0]] 
 ![![13, 0, 0], ![0, 1, 0], ![7, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![0, 1, 0], ![2, 1, 4], ![149, -27, -1]]]
  hmulB := by decide  
  f := ![![![-13, -7, -28], ![0, 91, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-7, -4, -15], ![3, 49, 0]]]
  g := ![![![1, 0, 0], ![0, 13, 0], ![-7, 0, 13]], ![![0, 1, 0], ![-2, 1, 4], ![12, -27, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-13, 1, 0]] 
 ![![19, 0, 0], ![6, 1, 0], ![9, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-13, 1, 0], ![2, -12, 4], ![149, -27, -14]]]
  hmulB := by decide  
  f := ![![![58, -573, 192], ![-57, -912, 0]], ![![18, -179, 60], ![-18, -285, 0]], ![![35, -272, 91], ![-16, -432, 0]]]
  g := ![![![1, 0, 0], ![-6, 19, 0], ![-9, 0, 19]], ![![-1, 1, 0], ![2, -12, 4], ![23, -27, -14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 19 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![13, 0, 0], ![0, 1, 0], ![7, 0, 1]] ![310563493677, -64302237730, -2097847190] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![25019109539, -64302237730, -2097847190]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![310563493681, -64302237730, -2097847190]
 hxeq :=  rfl
 m := 4
 C := ![310563493677, -64302237730, -2097847190]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![13, 0, 0], ![0, 1, 0], ![7, 0, 1]] ![-302689, 63841, 617] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-23616, 63841, 617]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-302684, 63841, 617]
 hxeq :=  rfl
 m := 5
 C := ![-302689, 63841, 617]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![19, 0, 0], ![6, 1, 0], ![9, 0, 1]] ![310563493675, -64302237730, -2097847190] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![37645133935, -64302237730, -2097847190]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![310563493681, -64302237730, -2097847190]
 hxeq :=  rfl
 m := 6
 C := ![310563493675, -64302237730, -2097847190]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 14
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![19, 0, 0], ![6, 1, 0], ![9, 0, 1]] ![-302697, 63841, 617] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-36384, 63841, 617]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-302684, 63841, 617]
 hxeq :=  rfl
 m := 13
 C := ![-302697, 63841, 617]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

end Sat3
