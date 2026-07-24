import IdealArithmetic.Examples.NF3_1_797796_1.ClassGroupData3_1_797796_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_797796_1.RI3_1_797796_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq19 : Fact $ Nat.Prime 19 := {out := by norm_num}
instance hq37 : Fact $ Nat.Prime 37 := {out := by norm_num}

def R19 : IsOrderOf (2 : ZMod 19) 18 where
 m := 2
 P := ![2, 3]
 e := ![1, 2]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R37 : IsOrderOf (2 : ZMod 37) 36 where
 m := 2
 P := ![2, 3]
 e := ![2, 2]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-1, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![37, 0, 0], ![14, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![19, 0, 0], ![-1, 1, 0]] 
 ![![19, 0, 0], ![18, 1, 0], ![9, 0, 1]] where
  M :=![![![19, 0, 0], ![0, 19, 0], ![0, 0, 19]], ![![-1, 1, 0], ![0, -1, 2], ![710, 117, -1]]]
  hmulB := by decide  
  f := ![![![4, -3, 0], ![57, 0, 0]], ![![2, -1, 0], ![20, 0, 0]], ![![2, -1, -1], ![29, 10, 0]]]
  g := ![![![1, 0, 0], ![-18, 19, 0], ![-9, 0, 19]], ![![-1, 1, 0], ![0, -1, 2], ![-73, 117, -1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 19 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![37, 0, 0], ![14, 1, 0]] 
 ![![37, 0, 0], ![14, 1, 0], ![13, 0, 1]] where
  M :=![![![37, 0, 0], ![0, 37, 0], ![0, 0, 37]], ![![14, 1, 0], ![0, 14, 2], ![710, 117, 14]]]
  hmulB := by decide  
  f := ![![![85, 6, 0], ![-222, 0, 0]], ![![14, 1, 0], ![-36, 0, 0]], ![![17, -6, -1], ![-44, 19, 0]]]
  g := ![![![1, 0, 0], ![-14, 37, 0], ![-13, 0, 37]], ![![0, 1, 0], ![-6, 14, 2], ![-30, 117, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 37 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![19, 0, 0], ![18, 1, 0], ![9, 0, 1]] ![97702965, -5104226, -46088] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![9999675, -5104226, -46088]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![97702967, -5104226, -46088]
 hxeq :=  rfl
 m := 2
 C := ![97702965, -5104226, -46088]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![19, 0, 0], ![18, 1, 0], ![9, 0, 1]] ![-209171, -46267, -5221] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![35296, -46267, -5221]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R19) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-209153, -46267, -5221]
 hxeq :=  rfl
 m := 18
 C := ![-209171, -46267, -5221]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![37, 0, 0], ![14, 1, 0], ![13, 0, 1]] ![97702946, -5104226, -46088] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![4588142, -5104226, -46088]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![97702967, -5104226, -46088]
 hxeq :=  rfl
 m := 21
 C := ![97702946, -5104226, -46088]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 22
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![37, 0, 0], ![14, 1, 0], ![13, 0, 1]] ![-209155, -46267, -5221] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![13688, -46267, -5221]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R37) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-209153, -46267, -5221]
 hxeq :=  rfl
 m := 2
 C := ![-209155, -46267, -5221]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

end Sat3
