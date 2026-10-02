import IdealArithmetic.MordellExamples.MordellExample2026.NF2_2_8104_1.ClassGroupData2_2_8104_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.MordellExamples.MordellExample2026.NF2_2_8104_1.RI2_2_8104_1

namespace NF2_2_8104_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat7 
instance hq29 : Fact $ Nat.Prime 29 := {out := by norm_num}
instance hq71 : Fact $ Nat.Prime 71 := {out := by norm_num}

def R29 : IsOrderOf (2 : ZMod 29) 28 where
 m := 2
 P := ![2, 7]
 e := ![2, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R71 : IsOrderOf (7 : ZMod 71) 70 where
 m := 3
 P := ![2, 5, 7]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0], ![5, 1]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![71, 0], ![31, 1]] i)))

def A0: IdealEqSpanCertificate' Table ![![29, 0], ![5, 1]] 
 ![![29, 0], ![5, 1]] where
  M :=![![![29, 0], ![0, 29]], ![![5, 1], ![2026, 5]]]
  hmulB := by decide  
  f := ![![![-4, -1], ![29, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-5, 29]], ![![0, 1], ![69, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 29 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![71, 0], ![31, 1]] 
 ![![71, 0], ![31, 1]] where
  M :=![![![71, 0], ![0, 71]], ![![31, 1], ![2026, 31]]]
  hmulB := by decide  
  f := ![![![-30, -1], ![71, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-31, 71]], ![![0, 1], ![15, 31]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 71 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![29, 0], ![5, 1]] ![24, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![1, -1]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 7 zeta1 3 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![45, -1]
 hxeq :=  rfl
 m := 21
 C := ![24, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 17
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![29, 0], ![5, 1]] ![4211, -80] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![159, -80]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 7 alpha0 1 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![4213, -80]
 hxeq :=  rfl
 m := 2
 C := ![4211, -80]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![71, 0], ![31, 1]] ![40, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![1, -1]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R71) ▸ IsPrimitiveRoot.orderOf _) 7 zeta1 0 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![45, -1]
 hxeq :=  rfl
 m := 5
 C := ![40, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 28
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![71, 0], ![31, 1]] ![4194, -80] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![94, -80]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R71) ▸ IsPrimitiveRoot.orderOf _) 7 alpha0 2 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![4213, -80]
 hxeq :=  rfl
 m := 19
 C := ![4194, -80]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 16
 hpow := by zmod_pow
 heql := by decide

end Sat7

end

end NF2_2_8104_1
