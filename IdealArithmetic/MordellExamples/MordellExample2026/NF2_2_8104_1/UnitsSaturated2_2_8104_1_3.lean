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

namespace Sat3 
instance hq61 : Fact $ Nat.Prime 61 := {out := by norm_num}

def R61 : IsOrderOf (2 : ZMod 61) 60 where
 m := 3
 P := ![2, 3, 5]
 e := ![2, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0], ![14, 1]] i)))

def A0: IdealEqSpanCertificate' Table ![![61, 0], ![14, 1]] 
 ![![61, 0], ![14, 1]] where
  M :=![![![61, 0], ![0, 61]], ![![14, 1], ![2026, 14]]]
  hmulB := by decide  
  f := ![![![-13, -1], ![61, 0]], ![![0, 0], ![1, 0]]]
  g := ![![![1, 0], ![-14, 61]], ![![0, 1], ![30, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 61 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def Log00Mem : IdealMemCertificate B I0
 ![![61, 0], ![14, 1]] ![-14, -1] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![0, -1]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![45, -1]
 hxeq :=  rfl
 m := 59
 C := ![-14, -1]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 31
 hpow := by zmod_pow
 heql := by decide

end Sat3

end

end NF2_2_8104_1
