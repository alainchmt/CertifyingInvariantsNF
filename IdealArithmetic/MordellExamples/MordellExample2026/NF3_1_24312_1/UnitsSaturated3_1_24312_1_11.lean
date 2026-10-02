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

namespace Sat11 
instance hq23 : Fact $ Nat.Prime 23 := {out := by norm_num}

def R23 : IsOrderOf (5 : ZMod 23) 22 where
 m := 2
 P := ![2, 11]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![5, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![23, 0, 0], ![5, 1, 0]] 
 ![![23, 0, 0], ![5, 1, 0], ![7, 0, 1]] where
  M :=![![![23, 0, 0], ![0, 23, 0], ![0, 0, 23]], ![![5, 1, 0], ![0, 5, 3], ![30, -1, 5]]]
  hmulB := by decide  
  f := ![![![51, 10, 0], ![-230, 0, 0]], ![![5, 1, 0], ![-22, 0, 0]], ![![9, 0, -1], ![-40, 8, 0]]]
  g := ![![![1, 0, 0], ![-5, 23, 0], ![-7, 0, 23]], ![![0, 1, 0], ![-2, 5, 3], ![0, -1, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 23 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def Log00Mem : IdealMemCertificate B I0
 ![![23, 0, 0], ![5, 1, 0], ![7, 0, 1]] ![178361260665498855294599509796, 35938665342336427911821503300, 25318107466978248199411982702] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-7763426883262218333060516766, 35938665342336427911821503300, 25318107466978248199411982702]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R23) ▸ IsPrimitiveRoot.orderOf _) 11 zeta1 1 where
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
 k := 1
 hpow := by zmod_pow
 heql := by decide

end Sat11
