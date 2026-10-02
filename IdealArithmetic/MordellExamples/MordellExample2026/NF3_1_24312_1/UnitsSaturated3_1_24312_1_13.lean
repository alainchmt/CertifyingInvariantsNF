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

namespace Sat13 
instance hq131 : Fact $ Nat.Prime 131 := {out := by norm_num}

def R131 : IsOrderOf (2 : ZMod 131) 130 where
 m := 3
 P := ![2, 5, 13]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![48, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![48, 1, 0]] 
 ![![131, 0, 0], ![48, 1, 0], ![18, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![48, 1, 0], ![0, 48, 3], ![30, -1, 48]]]
  hmulB := by decide  
  f := ![![![2353, 49, 0], ![-6419, 0, 0]], ![![816, 17, 0], ![-2226, 0, 0]], ![![294, -10, -1], ![-802, 44, 0]]]
  g := ![![![1, 0, 0], ![-48, 131, 0], ![-18, 0, 131]], ![![0, 1, 0], ![-18, 48, 3], ![-6, -1, 48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 131 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def Log00Mem : IdealMemCertificate B I0
 ![![131, 0, 0], ![48, 1, 0], ![18, 0, 1]] ![178361260665498855294599509747, 35938665342336427911821503300, 25318107466978248199411982702] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-15285653512765329405055330819, 35938665342336427911821503300, 25318107466978248199411982702]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R131) ▸ IsPrimitiveRoot.orderOf _) 13 zeta1 9 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![178361260665498855294599509801, 35938665342336427911821503300, 25318107466978248199411982702]
 hxeq :=  rfl
 m := 54
 C := ![178361260665498855294599509747, 35938665342336427911821503300, 25318107466978248199411982702]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 87
 hpow := by zmod_pow
 heql := by decide

end Sat13
