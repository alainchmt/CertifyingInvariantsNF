import IdealArithmetic.Examples.NF3_1_119660_3.ClassGroupData3_1_119660_3
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_119660_3.RI3_1_119660_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq13 : Fact $ Nat.Prime 13 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R13 : IsOrderOf (2 : ZMod 13) 12 where
 m := 2
 P := ![2, 3]
 e := ![2, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R7 : IsOrderOf (3 : ZMod 7) 6 where
 m := 2
 P := ![2, 3]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![3, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-2, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![3, 1, 0]] 
 ![![13, 0, 0], ![3, 1, 0], ![4, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![3, 1, 0], ![0, 3, 1], ![66, -8, 3]]]
  hmulB := by decide  
  f := ![![![16, 5, 0], ![-65, 0, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![4, 1, 0], ![-16, 1, 0]]]
  g := ![![![1, 0, 0], ![-3, 13, 0], ![-4, 0, 13]], ![![0, 1, 0], ![-1, 3, 1], ![6, -8, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![-2, 1, 0]] 
 ![![7, 0, 0], ![5, 1, 0], ![3, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![-2, 1, 0], ![0, -2, 1], ![66, -8, -2]]]
  hmulB := by decide  
  f := ![![![13, -6, 0], ![42, 0, 0]], ![![11, -5, 0], ![36, 0, 0]], ![![5, -2, 0], ![16, 1, 0]]]
  g := ![![![1, 0, 0], ![-5, 7, 0], ![-3, 0, 7]], ![![-1, 1, 0], ![1, -2, 1], ![16, -8, -2]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![13, 0, 0], ![3, 1, 0], ![4, 0, 1]] ![-237199173777, 98905888870, -8528996504] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-38446219567, 98905888870, -8528996504]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-237199173775, 98905888870, -8528996504]
 hxeq :=  rfl
 m := 2
 C := ![-237199173777, 98905888870, -8528996504]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![13, 0, 0], ![3, 1, 0], ![4, 0, 1]] ![92123748946, 16023408451, 4729239252] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![1933582045, 16023408451, 4729239252]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![92123748957, 16023408451, 4729239252]
 hxeq :=  rfl
 m := 11
 C := ![92123748946, 16023408451, 4729239252]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![5, 1, 0], ![3, 0, 1]] ![-237199173781, 98905888870, -8528996504] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-100877375517, 98905888870, -8528996504]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-237199173775, 98905888870, -8528996504]
 hxeq :=  rfl
 m := 6
 C := ![-237199173781, 98905888870, -8528996504]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![5, 1, 0], ![3, 0, 1]] ![92123748955, 16023408451, 4729239252] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-311573008, 16023408451, 4729239252]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![92123748957, 16023408451, 4729239252]
 hxeq :=  rfl
 m := 2
 C := ![92123748955, 16023408451, 4729239252]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

end Sat3
