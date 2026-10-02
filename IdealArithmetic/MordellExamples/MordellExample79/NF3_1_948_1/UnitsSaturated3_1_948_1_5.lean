import IdealArithmetic.MordellExamples.MordellExample79.NF3_1_948_1.UnitsData3_1_948_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.MordellExamples.MordellExample79.NF3_1_948_1.RI3_1_948_1

namespace NF3_1_948_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0], ![19, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![31, 0, 0], ![19, 1, 0]] 
 ![![31, 0, 0], ![19, 1, 0], ![20, 0, 1]] where
  M :=![![![31, 0, 0], ![0, 31, 0], ![0, 0, 31]], ![![19, 1, 0], ![-1, 18, 3], ![6, 3, -1]]]
  hmulB := by decide  
  f := ![![![90, -1945, -324], ![31, 3348, 0]], ![![47, -1189, -198], ![32, 2046, 0]], ![![55, -1255, -209], ![25, 2160, 0]]]
  g := ![![![1, 0, 0], ![-19, 31, 0], ![-20, 0, 31]], ![![0, 1, 0], ![-13, 18, 3], ![-1, 3, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def Log00Mem : IdealMemCertificate B I0
 ![![31, 0, 0], ![19, 1, 0], ![20, 0, 1]] ![-65, -24, 173] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-99, -24, 173]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-52, -24, 173]
 hxeq :=  rfl
 m := 13
 C := ![-65, -24, 173]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 11
 hpow := by zmod_pow
 heql := by decide

end Sat5

end

end NF3_1_948_1
