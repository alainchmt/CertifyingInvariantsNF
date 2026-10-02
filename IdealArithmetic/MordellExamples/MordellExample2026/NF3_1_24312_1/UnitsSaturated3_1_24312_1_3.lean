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

namespace Sat3 
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R7 : IsOrderOf (3 : ZMod 7) 6 where
 m := 2
 P := ![2, 3]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![7, 0, 0], ![3, 1, 0]] 
 ![![7, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![3, 1, 0], ![0, 3, 3], ![30, -1, 3]]]
  hmulB := by decide  
  f := ![![![4, 1, 0], ![-7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![4, -1, -2], ![-8, 5, 0]]]
  g := ![![![1, 0, 0], ![-3, 7, 0], ![-4, 0, 7]], ![![0, 1, 0], ![-3, 3, 3], ![3, -1, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def Log00Mem : IdealMemCertificate B I0
 ![![7, 0, 0], ![3, 1, 0], ![4, 0, 1]] ![178361260665498855294599509796, 35938665342336427911821503300, 25318107466978248199411982702] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-4389595032774774462644704416, 35938665342336427911821503300, 25318107466978248199411982702]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![178361260665498855294599509801, 35938665342336427911821503300, 25318107466978248199411982702]
 hxeq :=  rfl
 m := 5
 C := ![178361260665498855294599509796, 35938665342336427911821503300, 25318107466978248199411982702]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

end Sat3
