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

namespace Sat19 
instance hq229 : Fact $ Nat.Prime 229 := {out := by norm_num}

def R229 : IsOrderOf (6 : ZMod 229) 228 where
 m := 3
 P := ![2, 3, 19]
 e := ![2, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![229, 0, 0], ![-49, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![229, 0, 0], ![-49, 1, 0]] 
 ![![229, 0, 0], ![180, 1, 0], ![192, 0, 1]] where
  M :=![![![229, 0, 0], ![0, 229, 0], ![0, 0, 229]], ![![-49, 1, 0], ![0, -49, 3], ![30, -1, -49]]]
  hmulB := by decide  
  f := ![![![10830, -221, 0], ![50609, 0, 0]], ![![8576, -175, 0], ![40076, 0, 0]], ![![9102, -153, -2], ![42534, 153, 0]]]
  g := ![![![1, 0, 0], ![-180, 229, 0], ![-192, 0, 229]], ![![-1, 1, 0], ![36, -49, 3], ![42, -1, -49]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 229 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def Log00Mem : IdealMemCertificate B I0
 ![![229, 0, 0], ![180, 1, 0], ![192, 0, 1]] ![178361260665498855294599509750, 35938665342336427911821503300, 25318107466978248199411982702] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-48697271330195990493975422546, 35938665342336427911821503300, 25318107466978248199411982702]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R229) ▸ IsPrimitiveRoot.orderOf _) 19 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![178361260665498855294599509801, 35938665342336427911821503300, 25318107466978248199411982702]
 hxeq :=  rfl
 m := 51
 C := ![178361260665498855294599509750, 35938665342336427911821503300, 25318107466978248199411982702]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 40
 hpow := by zmod_pow
 heql := by decide

end Sat19
