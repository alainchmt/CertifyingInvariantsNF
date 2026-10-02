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

namespace Sat23 
instance hq47 : Fact $ Nat.Prime 47 := {out := by norm_num}

def R47 : IsOrderOf (5 : ZMod 47) 46 where
 m := 2
 P := ![2, 23]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![47, 0, 0], ![1, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![47, 0, 0], ![1, 1, 0]] 
 ![![47, 0, 0], ![1, 1, 0], ![31, 0, 1]] where
  M :=![![![47, 0, 0], ![0, 47, 0], ![0, 0, 47]], ![![1, 1, 0], ![0, 1, 3], ![30, -1, 1]]]
  hmulB := by decide  
  f := ![![![0, -1, 0], ![47, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, -1, -1], ![31, 16, 0]]]
  g := ![![![1, 0, 0], ![-1, 47, 0], ![-31, 0, 47]], ![![0, 1, 0], ![-2, 1, 3], ![0, -1, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 47 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def Log00Mem : IdealMemCertificate B I0
 ![![47, 0, 0], ![1, 1, 0], ![31, 0, 1]] ![178361260665498855294599509762, 35938665342336427911821503300, 25318107466978248199411982702] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-13668909279854537591467945900, 35938665342336427911821503300, 25318107466978248199411982702]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R47) ▸ IsPrimitiveRoot.orderOf _) 23 zeta1 8 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![178361260665498855294599509801, 35938665342336427911821503300, 25318107466978248199411982702]
 hxeq :=  rfl
 m := 39
 C := ![178361260665498855294599509762, 35938665342336427911821503300, 25318107466978248199411982702]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 31
 hpow := by zmod_pow
 heql := by decide

end Sat23
