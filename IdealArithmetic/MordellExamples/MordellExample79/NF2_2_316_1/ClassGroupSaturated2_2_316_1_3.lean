import IdealArithmetic.MordellExamples.MordellExample79.NF2_2_316_1.ClassGroupData2_2_316_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.MordellExamples.MordellExample79.NF2_2_316_1.RI2_2_316_1

namespace NF2_2_316_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
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
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0], ![1, 1]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0], ![3, 1]] 
 ![![7, 0], ![3, 1]] where
  M :=![![![7, 0], ![0, 7]], ![![3, 1], ![79, 3]]]
  hmulB := by decide  
  f := ![![![-2, -1], ![7, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-3, 7]], ![![0, 1], ![10, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![13, 0], ![1, 1]] 
 ![![13, 0], ![1, 1]] where
  M :=![![![13, 0], ![0, 13]], ![![1, 1], ![79, 1]]]
  hmulB := by decide  
  f := ![![![0, -1], ![13, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-1, 13]], ![![0, 1], ![6, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![7, 0], ![3, 1]] ![76, 9] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![7, 9]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![80, 9]
 hxeq :=  rfl
 m := 4
 C := ![76, 9]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![7, 0], ![3, 1]] ![-22, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-4, 2]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-17, 2]
 hxeq :=  rfl
 m := 5
 C := ![-22, 2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![13, 0], ![1, 1]] ![74, 9] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![5, 9]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![80, 9]
 hxeq :=  rfl
 m := 6
 C := ![74, 9]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![13, 0], ![1, 1]] ![-24, 2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-2, 2]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-17, 2]
 hxeq :=  rfl
 m := 7
 C := ![-24, 2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 11
 hpow := by zmod_pow
 heql := by decide

end Sat3

end

end NF2_2_316_1
