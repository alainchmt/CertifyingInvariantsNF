import IdealArithmetic.MordellExamples.MordellExample17.NF3_1_459_1.UnitsData3_1_459_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.MordellExamples.MordellExample17.NF3_1_459_1.RI3_1_459_1

namespace NF3_1_459_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat2 
instance hq3 : Fact $ Nat.Prime 3 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-3, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![1, 1, 0]] 
 ![![3, 0, 0], ![1, 1, 0], ![0, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![1, 1, 0], ![0, 0, 2], ![4, -2, 2]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 2, 0]]]
  g := ![![![1, 0, 0], ![-1, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![0, 0, 2], ![2, -2, 2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-3, 1, 0]] 
 ![![7, 0, 0], ![4, 1, 0], ![1, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-3, 1, 0], ![0, -4, 2], ![4, -2, -2]]]
  hmulB := by decide  
  f := ![![![4, 15, -8], ![7, 28, 0]], ![![1, 8, -4], ![1, 14, 0]], ![![1, 2, -1], ![2, 4, 0]]]
  g := ![![![1, 0, 0], ![-4, 7, 0], ![-1, 0, 7]], ![![-1, 1, 0], ![2, -4, 2], ![2, -2, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![1, 1, 0], ![0, 0, 1]] ![20, 2, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![6, 2, 8]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![21, 2, 8]
 hxeq :=  rfl
 m := 1
 C := ![20, 2, 8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![1, 1, 0], ![0, 0, 1]] ![-3, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 0]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-3, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![4, 1, 0], ![1, 0, 1]] ![16, 2, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, 2, 8]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![21, 2, 8]
 hxeq :=  rfl
 m := 5
 C := ![16, 2, 8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![4, 1, 0], ![1, 0, 1]] ![-7, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 6
 C := ![-7, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

end Sat2

end

end NF3_1_459_1
