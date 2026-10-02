import IdealArithmetic.MordellExamples.MordellExample142.NF2_2_568_1.ClassGroupData2_2_568_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.MordellExamples.MordellExample142.NF2_2_568_1.RI2_2_568_1

namespace NF2_2_568_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq19 : Fact $ Nat.Prime 19 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R19 : IsOrderOf (2 : ZMod 19) 18 where
 m := 2
 P := ![2, 3]
 e := ![1, 2]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0], ![3, 1]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0], ![3, 1]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0], ![3, 1]] 
 ![![7, 0], ![3, 1]] where
  M :=![![![7, 0], ![0, 7]], ![![3, 1], ![142, 3]]]
  hmulB := by decide  
  f := ![![![-2, -1], ![7, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-3, 7]], ![![0, 1], ![19, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![19, 0], ![3, 1]] 
 ![![19, 0], ![3, 1]] where
  M :=![![![19, 0], ![0, 19]], ![![3, 1], ![142, 3]]]
  hmulB := by decide  
  f := ![![![-2, -1], ![19, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-3, 19]], ![![0, 1], ![7, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 19 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![7, 0], ![3, 1]] ![141, 12] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![15, 12]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![143, 12]
 hxeq :=  rfl
 m := 2
 C := ![141, 12]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![7, 0], ![3, 1]] ![-18, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-3, 1]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-13, 1]
 hxeq :=  rfl
 m := 5
 C := ![-18, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![19, 0], ![3, 1]] ![131, 12] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![5, 12]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![143, 12]
 hxeq :=  rfl
 m := 12
 C := ![131, 12]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 15
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![19, 0], ![3, 1]] ![-16, 1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 1]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-13, 1]
 hxeq :=  rfl
 m := 3
 C := ![-16, 1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 13
 hpow := by zmod_pow
 heql := by decide

end Sat3

end

end NF2_2_568_1
