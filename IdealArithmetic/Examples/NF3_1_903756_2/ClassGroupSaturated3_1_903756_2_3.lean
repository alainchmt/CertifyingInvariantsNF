import IdealArithmetic.Examples.NF3_1_903756_2.ClassGroupData3_1_903756_2
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_903756_2.RI3_1_903756_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq19 : Fact $ Nat.Prime 19 := {out := by norm_num}
instance hq7 : Fact $ Nat.Prime 7 := {out := by norm_num}

def R19 : IsOrderOf (2 : ZMod 19) 18 where
 m := 2
 P := ![2, 3]
 e := ![1, 2]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![1, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![1, 1, 0]] 
 ![![19, 0, 0], ![1, 1, 0], ![16, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![1, 1, 0], ![4, -1, 11], ![183, 5, 4]]]
  hmulB := by decide  
  f := ![![![-15, 4, -44], ![0, 76, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![-13, 3, -37], ![7, 64, 0]]]
  g := ![![![1, 0, 0], ![-1, 19, 0], ![-16, 0, 19]], ![![0, 1, 0], ![-9, -1, 11], ![6, 5, 4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 19 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![2, 1, 0]] 
 ![![7, 0, 0], ![2, 1, 0], ![1, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![4, 0, 11], ![183, 5, 5]]]
  hmulB := by decide  
  f := ![![![45, -2, 132], ![14, -84, 0]], ![![10, -1, 33], ![8, -21, 0]], ![![5, -1, 19], ![7, -12, 0]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![-1, 0, 7]], ![![0, 1, 0], ![-1, 0, 11], ![24, 5, 5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![19, 0, 0], ![1, 1, 0], ![16, 0, 1]] ![-1909480242515008478307664281449908943545, -159266905049960344906125831398318743530, -149829100178205939929563802226005021044] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![34055382388749837130078020292867901931, -159266905049960344906125831398318743530, -149829100178205939929563802226005021044]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1909480242515008478307664281449908943535, -159266905049960344906125831398318743530, -149829100178205939929563802226005021044]
 hxeq :=  rfl
 m := 10
 C := ![-1909480242515008478307664281449908943545, -159266905049960344906125831398318743530, -149829100178205939929563802226005021044]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 17
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![19, 0, 0], ![1, 1, 0], ![16, 0, 1]] ![-50399300, 2697030, 491129] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-3208126, 2697030, 491129]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-50399288, 2697030, 491129]
 hxeq :=  rfl
 m := 12
 C := ![-50399300, 2697030, 491129]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 15
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![2, 1, 0], ![1, 0, 1]] ![-1909480242515008478307664281449908943541, -159266905049960344906125831398318743530, -149829100178205939929563802226005021044] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-205873904605268835509406973775323776491, -159266905049960344906125831398318743530, -149829100178205939929563802226005021044]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1909480242515008478307664281449908943535, -159266905049960344906125831398318743530, -149829100178205939929563802226005021044]
 hxeq :=  rfl
 m := 6
 C := ![-1909480242515008478307664281449908943541, -159266905049960344906125831398318743530, -149829100178205939929563802226005021044]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![2, 1, 0], ![1, 0, 1]] ![-50399291, 2697030, 491129] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-8040640, 2697030, 491129]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-50399288, 2697030, 491129]
 hxeq :=  rfl
 m := 3
 C := ![-50399291, 2697030, 491129]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

end Sat3
