import IdealArithmetic.Examples.NF3_1_912968_1.ClassGroupData3_1_912968_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF3_1_912968_1.RI3_1_912968_1

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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![0, 1, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![13, 0, 0], ![0, 1, 0]] 
 ![![13, 0, 0], ![0, 1, 0], ![7, 0, 1]] where
  M :=![![![13, 0, 0], ![0, 13, 0], ![0, 0, 13]], ![![0, 1, 0], ![1, 0, 2], ![189, 25, 1]]]
  hmulB := by decide  
  f := ![![![0, 0, -2], ![0, 13, 0]], ![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 7, 0]]]
  g := ![![![1, 0, 0], ![0, 13, 0], ![-7, 0, 13]], ![![0, 1, 0], ![-1, 0, 2], ![14, 25, 1]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 13 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![7, 0, 0], ![2, 1, 0]] 
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] where
  M :=![![![7, 0, 0], ![0, 7, 0], ![0, 0, 7]], ![![2, 1, 0], ![1, 2, 2], ![189, 25, 3]]]
  hmulB := by decide  
  f := ![![![-13, -31, -32], ![-7, 112, 0]], ![![-4, -8, -8], ![1, 28, 0]], ![![-4, -9, -9], ![-1, 32, 0]]]
  g := ![![![1, 0, 0], ![-2, 7, 0], ![-2, 0, 7]], ![![0, 1, 0], ![-1, 2, 2], ![19, 25, 3]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 7 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def Log00Mem : IdealMemCertificate B I0
 ![![13, 0, 0], ![0, 1, 0], ![7, 0, 1]] ![10952044939719060747743573477669218572084246, 2516705080517467303739331740959113213581241, 562843843852040622970894997957372481241162] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![539395233288828952842100653228277784876624, 2516705080517467303739331740959113213581241, 562843843852040622970894997957372481241162]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![10952044939719060747743573477669218572084256, 2516705080517467303739331740959113213581241, 562843843852040622970894997957372481241162]
 hxeq :=  rfl
 m := 10
 C := ![10952044939719060747743573477669218572084246, 2516705080517467303739331740959113213581241, 562843843852040622970894997957372481241162]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 10
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![13, 0, 0], ![0, 1, 0], ![7, 0, 1]] ![-44653, -71, 927] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-3934, -71, 927]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R13) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-44652, -71, 927]
 hxeq :=  rfl
 m := 1
 C := ![-44653, -71, 927]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] ![10952044939719060747743573477669218572084255, 2516705080517467303739331740959113213581241, 562843843852040622970894997957372481241162] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![684706727282863556331874285690892454634207, 2516705080517467303739331740959113213581241, 562843843852040622970894997957372481241162]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![10952044939719060747743573477669218572084256, 2516705080517467303739331740959113213581241, 562843843852040622970894997957372481241162]
 hxeq :=  rfl
 m := 1
 C := ![10952044939719060747743573477669218572084255, 2516705080517467303739331740959113213581241, 562843843852040622970894997957372481241162]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![7, 0, 0], ![2, 1, 0], ![2, 0, 1]] ![-44656, -71, 927] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-6624, -71, 927]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 3
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-44652, -71, 927]
 hxeq :=  rfl
 m := 4
 C := ![-44656, -71, 927]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

end Sat3
