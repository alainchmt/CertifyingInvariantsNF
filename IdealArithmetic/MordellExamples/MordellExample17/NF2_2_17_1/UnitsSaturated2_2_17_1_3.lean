import IdealArithmetic.MordellExamples.MordellExample17.NF2_2_17_1.ClassGroupData2_2_17_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.MordellExamples.MordellExample17.NF2_2_17_1.RI2_2_17_1

namespace NF2_2_17_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0], ![-3, 2]] i)))

def A0: IdealEqSpanCertificate' Table ![![13, 0], ![-3, 2]] 
 ![![13, 0], ![5, 1]] where
  M :=![![![13, 0], ![0, 13]], ![![-3, 2], ![8, -1]]]
  hmulB := by decide  
  f := ![![![1, 0], ![0, 0]], ![![2, -1], ![7, 0]]]
  g := ![![![1, 0], ![-5, 13]], ![![-1, 2], ![1, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def Log00Mem : IdealMemCertificate B I0
 ![![13, 0], ![5, 1]] ![3, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![1, -2]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 2
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![5, -2]
 hxeq :=  rfl
 m := 2
 C := ![3, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

end Sat3

end

end NF2_2_17_1
