import IdealArithmetic.Examples.NF3_1_975819_1.ClassGroupData3_1_975819_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_975819_1.RI3_1_975819_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat2 
instance hq3 : Fact $ Nat.Prime 3 := {out := by norm_num}
instance hq5 : Fact $ Nat.Prime 5 := {out := by norm_num}

def R3 : IsOrderOf (2 : ZMod 3) 2 where
 m := 1
 P := ![2]
 e := ![1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R5 : IsOrderOf (2 : ZMod 5) 4 where
 m := 1
 P := ![2]
 e := ![2]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-26, 1, 1]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![2, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![3, 0, 0], ![0, 1, 0]] 
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![0, 1, 0], ![-2, 2, 5], ![-296, 39, -1]]]
  hmulB := by decide  
  f := ![![![-3, 3, 10], ![3, -6, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-2, 2, 7], ![2, -4, 0]]]
  g := ![![![1, 0, 0], ![0, 3, 0], ![-2, 0, 3]], ![![0, 1, 0], ![-4, 2, 5], ![-98, 39, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![5, 0, 0], ![-26, 1, 1]] 
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] where
  M :=![![![5, 0, 0], ![0, 5, 0], ![0, 0, 5]], ![![-26, 1, 1], ![-298, 15, 4], ![-134, -28, 13]]]
  hmulB := by decide  
  f := ![![![97, -32, 56], ![-440, 40, 0]], ![![25, -5, 8], ![-64, 6, 0]], ![![53, -19, 34], ![-265, 24, 0]]]
  g := ![![![1, 0, 0], ![-1, 5, 0], ![-3, 0, 5]], ![![-6, 1, 1], ![-65, 15, 4], ![-29, -28, 13]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 5 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![3, 0, 0], ![2, 1, 0]] 
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![3, 0, 0], ![0, 3, 0], ![0, 0, 3]], ![![2, 1, 0], ![-2, 4, 5], ![-296, 39, 1]]]
  hmulB := by decide  
  f := ![![![3, -9, -10], ![3, 6, 0]], ![![2, -4, -5], ![1, 3, 0]], ![![1, -3, -3], ![1, 2, 0]]]
  g := ![![![1, 0, 0], ![-2, 3, 0], ![-1, 0, 3]], ![![0, 1, 0], ![-5, 4, 5], ![-125, 39, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] ![1192750189641302820072362337334571632660907348, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![455899107312767672514053359251836144786824854, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1192750189641302820072362337334571632660907349, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607]
 hxeq :=  rfl
 m := 1
 C := ![1192750189641302820072362337334571632660907348, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] ![-3, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 0]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-3, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![3, 0, 0], ![0, 1, 0], ![2, 0, 1]] ![-35068446766, 6111685617, -1984294325] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-10366619372, 6111685617, -1984294325]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-35068446765, 6111685617, -1984294325]
 hxeq :=  rfl
 m := 1
 C := ![-35068446766, 6111685617, -1984294325]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] ![1192750189641302820072362337334571632660907346, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![341296337828020086451244152117167822558891125, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1192750189641302820072362337334571632660907349, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607]
 hxeq :=  rfl
 m := 3
 C := ![1192750189641302820072362337334571632660907346, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] ![-5, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 4
 C := ![-5, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![5, 0, 0], ![1, 1, 0], ![3, 0, 1]] ![-35068446768, 6111685617, -1984294325] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-7045449882, 6111685617, -1984294325]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-35068446765, 6111685617, -1984294325]
 hxeq :=  rfl
 m := 3
 C := ![-35068446768, 6111685617, -1984294325]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] ![1192750189641302820072362337334571632660907348, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![594281785965465850255194944261588196226361957, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1192750189641302820072362337334571632660907349, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607]
 hxeq :=  rfl
 m := 1
 C := ![1192750189641302820072362337334571632660907348, -251310801053297315979161812619862277584197458, -87473566148500098734898870210468400849783607]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] ![-3, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, 0]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-3, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![3, 0, 0], ![2, 1, 0], ![1, 0, 1]] ![-35068446767, 6111685617, -1984294325] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-15102507892, 6111685617, -1984294325]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-35068446765, 6111685617, -1984294325]
 hxeq :=  rfl
 m := 2
 C := ![-35068446767, 6111685617, -1984294325]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

end Sat2
