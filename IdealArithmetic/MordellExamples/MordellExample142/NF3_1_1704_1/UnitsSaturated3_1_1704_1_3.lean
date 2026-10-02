import IdealArithmetic.MordellExamples.MordellExample142.NF3_1_1704_1.UnitsData3_1_1704_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.MordellExamples.MordellExample142.NF3_1_1704_1.RI3_1_1704_1

namespace NF3_1_1704_1

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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![2, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![2, 1, 0]] 
 ![![13, 0, 0], ![2, 1, 0], ![4, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![2, 1, 0], ![-1, 0, 3], ![-31, -13, -11]]]
  hmulB := by decide  
  f := ![![![-13, 0, 42], ![0, -182, 0]], ![![-2, 0, 6], ![1, -26, 0]], ![![-4, 0, 13], ![0, -56, 0]]]
  g := ![![![1, 0, 0], ![-2, 13, 0], ![-4, 0, 13]], ![![0, 1, 0], ![-1, 0, 3], ![3, -13, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def Log00Mem : IdealMemCertificate B I0
 ![![13, 0, 0], ![2, 1, 0], ![4, 0, 1]] ![231636, 86541, 64071] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-15210, 86541, 64071]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![231646, 86541, 64071]
 hxeq :=  rfl
 m := 10
 C := ![231636, 86541, 64071]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 10
 hpow := by zmod_pow
 heql := by decide

end Sat3

end

end NF3_1_1704_1
