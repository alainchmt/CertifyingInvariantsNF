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

namespace Sat5 
instance hq131 : Fact $ Nat.Prime 131 := {out := by norm_num}

def R131 : IsOrderOf (2 : ZMod 131) 130 where
 m := 3
 P := ![2, 5, 13]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0], ![-35, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![131, 0, 0], ![-35, 1, 0]] 
 ![![131, 0, 0], ![96, 1, 0], ![92, 0, 1]] where
  M :=![![![131, 0, 0], ![0, 131, 0], ![0, 0, 131]], ![![-35, 1, 0], ![-1, -37, 3], ![-31, -13, -48]]]
  hmulB := by decide  
  f := ![![![-7887, -291856, 23664], ![0, -1033328, 0]], ![![-5779, -213860, 17340], ![1, -757180, 0]], ![![-5559, -204967, 16619], ![-75, -725696, 0]]]
  g := ![![![1, 0, 0], ![-96, 131, 0], ![-92, 0, 131]], ![![-1, 1, 0], ![25, -37, 3], ![43, -13, -48]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 131 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def Log00Mem : IdealMemCertificate B I0
 ![![131, 0, 0], ![96, 1, 0], ![92, 0, 1]] ![231580, 86541, 64071] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-106648, 86541, 64071]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R131) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 4 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![231646, 86541, 64071]
 hxeq :=  rfl
 m := 66
 C := ![231580, 86541, 64071]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 129
 hpow := by zmod_pow
 heql := by decide

end Sat5

end

end NF3_1_1704_1
