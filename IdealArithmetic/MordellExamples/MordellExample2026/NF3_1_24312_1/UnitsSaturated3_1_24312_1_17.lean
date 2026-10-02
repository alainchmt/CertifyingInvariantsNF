import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.UnitsData3_1_24312_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.MordellExamples.MordellExample2026.NF3_1_24312_1.RI3_1_24312_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat17 
instance hq103 : Fact $ Nat.Prime 103 := {out := by norm_num}

def R103 : IsOrderOf (5 : ZMod 103) 102 where
 m := 3
 P := ![2, 3, 17]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![103, 0, 0], ![12, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![103, 0, 0], ![12, 1, 0]] 
 ![![103, 0, 0], ![12, 1, 0], ![55, 0, 1]] where
  M :=![![![103, 0, 0], ![0, 103, 0], ![0, 0, 103]], ![![12, 1, 0], ![0, 12, 3], ![30, -1, 12]]]
  hmulB := by decide  
  f := ![![![445, 37, 0], ![-3811, 0, 0]], ![![36, 3, 0], ![-308, 0, 0]], ![![229, 11, -2], ![-1961, 69, 0]]]
  g := ![![![1, 0, 0], ![-12, 103, 0], ![-55, 0, 103]], ![![0, 1, 0], ![-3, 12, 3], ![-6, -1, 12]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 103 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def Log00Mem : IdealMemCertificate B I0
 ![![103, 0, 0], ![12, 1, 0], ![55, 0, 1]] ![178361260665498855294599509703, 35938665342336427911821503300, 25318107466978248199411982702] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-15974744020644096413737063869, 35938665342336427911821503300, 25318107466978248199411982702]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R103) ▸ IsPrimitiveRoot.orderOf _) 17 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![178361260665498855294599509801, 35938665342336427911821503300, 25318107466978248199411982702]
 hxeq :=  rfl
 m := 98
 C := ![178361260665498855294599509703, 35938665342336427911821503300, 25318107466978248199411982702]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 52
 hpow := by zmod_pow
 heql := by decide

end Sat17
