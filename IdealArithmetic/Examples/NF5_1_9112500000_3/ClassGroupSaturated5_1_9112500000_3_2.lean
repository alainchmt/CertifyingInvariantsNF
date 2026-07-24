import IdealArithmetic.Examples.NF5_1_9112500000_3.ClassGroupData5_1_9112500000_3
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_9112500000_3.RI5_1_9112500000_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat2 
instance hq11 : Fact $ Nat.Prime 11 := {out := by norm_num}
instance hq3 : Fact $ Nat.Prime 3 := {out := by norm_num}
instance hq29 : Fact $ Nat.Prime 29 := {out := by norm_num}

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R3 : IsOrderOf (2 : ZMod 3) 2 where
 m := 1
 P := ![2]
 e := ![1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R29 : IsOrderOf (2 : ZMod 29) 28 where
 m := 2
 P := ![2, 7]
 e := ![2, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![12, 0, 1, 2, 4]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![29, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![12, 0, 1, 2, 4]] 
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![12, 0, 1, 2, 4], ![60, -45, 0, -10, 0], ![-60, 10, -25, -60, -120], ![-210, 190, 1, 40, 0], ![84, -75, 4, -6, 18]]]
  hmulB := by decide  
  f := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![33710, -112123, -12338, -51150, -51900], ![27465, -7564, -382, -1, 0]], ![![33546, -111590, -12278, -50904, -51648], ![27336, -7528, -380, -1, 0]], ![![-16, 30, 2, 11, 8], ![-6, 2, 0, 0, 0]], ![![-33542, 111530, 12272, 50878, 51623], ![-27317, 7524, 380, 1, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![4, 0, 1, 2, 4], ![20, -45, 0, -10, 0], ![-20, 10, -25, -60, -120], ![-70, 190, 1, 40, 0], ![28, -75, 4, -6, 18]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] where
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![1, 1, 0, 0, 0], ![0, 1, 1, 0, 0], ![0, 5, 1, 10, 0], ![6, 5, -2, 7, 12], ![12, -18, 1, -8, -5]]]
  hmulB := by decide  
  f := ![![![80, 165, 34, 408, -20], ![-93, 42, -132, 0, -12]], ![![38, 81, 17, 204, -10], ![-41, 21, -66, 0, -6]], ![![78, 155, 34, 388, -20], ![-88, 37, -126, 0, -12]], ![![40, 85, 17, 211, -10], ![-46, 23, -68, 0, -6]], ![![52, 109, 23, 272, -13], ![-58, 27, -88, 0, -8]]]
  g := ![![![1, 0, 0, 0, 0], ![-1, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![-2, 0, 0, 3, 0], ![-2, 0, 0, 0, 3]], ![![0, 1, 0, 0, 0], ![-1, 1, 1, 0, 0], ![-9, 5, 1, 10, 0], ![-11, 5, -2, 7, 12], ![18, -18, 1, -8, -5]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 3 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![2, 1, 0, 0, 0], ![0, 2, 1, 0, 0], ![0, 5, 2, 10, 0], ![6, 5, -2, 8, 12], ![12, -18, 1, -8, -4]]]
  hmulB := by decide  
  f := ![![![31881, 99466, 33015, 173712, 288], ![-174548, 18051, -190872, -264, 0]], ![![10614, 33119, 10993, 57844, 96], ![-58112, 6017, -63558, -88, 0]], ![![21249, 66293, 22004, 115778, 192], ![-116338, 12035, -127215, -176, 0]], ![![5314, 16582, 5504, 28963, 48], ![-29094, 3016, -31824, -44, 0]], ![![14491, 45212, 15007, 78960, 131], ![-79338, 8203, -86760, -120, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 11, 0, 0, 0], ![-7, 0, 11, 0, 0], ![-2, 0, 0, 11, 0], ![-5, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![-1, 2, 1, 0, 0], ![-4, 5, 2, 10, 0], ![-6, 5, -2, 8, 12], ![7, -18, 1, -8, -4]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def A3: IdealEqSpanCertificate' Table ![![29, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] 
 ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] where
  M :=![![![29, 0, 0, 0, 0], ![0, 29, 0, 0, 0], ![0, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![0, 0, 0, 0, 29]], ![![-11, 1, 0, 0, 0], ![0, -11, 1, 0, 0], ![0, 5, -11, 10, 0], ![6, 5, -2, -5, 12], ![12, -18, 1, -8, -17]]]
  hmulB := by decide  
  f := ![![![288475, 2554, -76068, 66700, 5520], ![753246, -21808, -200100, -13340, 0]], ![![188130, 1671, -49610, 43500, 3600], ![491232, -14210, -130500, -8700, 0]], ![![238312, 2112, -62839, 55100, 4560], ![622264, -18008, -165300, -11020, 0]], ![![22, -1, 1, -1, 0], ![58, 4, 3, 0, 0]], ![![258632, 2291, -68199, 59800, 4949], ![675322, -19549, -179400, -11960, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-18, 29, 0, 0, 0], ![-24, 0, 29, 0, 0], ![0, 0, 0, 29, 0], ![-26, 0, 0, 0, 29]], ![![-1, 1, 0, 0, 0], ![6, -11, 1, 0, 0], ![6, 5, -11, 10, 0], ![-12, 5, -2, -5, 12], ![26, -18, 1, -8, -17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N3 : Nat.card (O ⧸ I3) = 29 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)

def Log00Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-68079, 251247, 79053, 269863, 369426] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-22693, 251247, 79053, 269863, 369426]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-68078, 251247, 79053, 269863, 369426]
 hxeq :=  rfl
 m := 1
 C := ![-68079, 251247, 79053, 269863, 369426]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![72669884397944627058787560488909268342246905517, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![24223294799314875686262520162969756114082301839, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![72669884397944627058787560488909268342246905518, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]
 hxeq :=  rfl
 m := 1
 C := ![72669884397944627058787560488909268342246905517, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-3, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log03Mem : IdealMemCertificate B I0
 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]] ![-1228505867337897533374795968991419417, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-409501955779299177791598656330473139, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1228505867337897533374795968991419416, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]
 hxeq :=  rfl
 m := 1
 C := ![-1228505867337897533374795968991419417, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log03Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-68080, 251247, 79053, 269863, 369426] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-585337, 251247, 79053, 269863, 369426]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-68078, 251247, 79053, 269863, 369426]
 hxeq :=  rfl
 m := 2
 C := ![-68080, 251247, 79053, 269863, 369426]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![72669884397944627058787560488909268342246905517, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![83923022635056620774630968636878632456724200648, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![72669884397944627058787560488909268342246905518, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]
 hxeq :=  rfl
 m := 1
 C := ![72669884397944627058787560488909268342246905517, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 0
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-3, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log13Mem : IdealMemCertificate B I1
 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![2, 0, 0, 0, 1]] ![-1228505867337897533374795968991419418, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-256254114978902064642294956905340226, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1228505867337897533374795968991419416, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]
 hxeq :=  rfl
 m := 2
 C := ![-1228505867337897533374795968991419418, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log13Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-68083, 251247, 79053, 269863, 369426] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-319164, 251247, 79053, 269863, 369426]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-68078, 251247, 79053, 269863, 369426]
 hxeq :=  rfl
 m := 5
 C := ![-68083, 251247, 79053, 269863, 369426]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 4
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![72669884397944627058787560488909268342246905510, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![36406813500585645303534000582369536972244833007, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![72669884397944627058787560488909268342246905518, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]
 hxeq :=  rfl
 m := 8
 C := ![72669884397944627058787560488909268342246905510, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-11, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 10
 C := ![-11, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log23Mem : IdealMemCertificate B I2
 ![![11, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![7, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-1228505867337897533374795968991419426, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-16907757659269339345303969797695780, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1228505867337897533374795968991419416, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]
 hxeq :=  rfl
 m := 10
 C := ![-1228505867337897533374795968991419426, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log23Mem
 k := 5
 hpow := by zmod_pow
 heql := by decide

def Log30Mem : IdealMemCertificate B I3
 ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] ![-68089, 251247, 79053, 269863, 369426] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-554927, 251247, 79053, 269863, 369426]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-68078, 251247, 79053, 269863, 369426]
 hxeq :=  rfl
 m := 11
 C := ![-68089, 251247, 79053, 269863, 369426]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log30Mem
 k := 25
 hpow := by zmod_pow
 heql := by decide

def Log31Mem : IdealMemCertificate B I3
 ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] ![72669884397944627058787560488909268342246905498, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![73657315215568578974323212439154518821917211756, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![72669884397944627058787560488909268342246905518, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]
 hxeq :=  rfl
 m := 20
 C := ![72669884397944627058787560488909268342246905498, -82985971093890408022594220611166386447259808587, 3735936183153940820862254239694302055990969, -26147479080084701663246027607699450796542032423, -21912863062765865898830397051820364795846902466]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log31Mem
 k := 24
 hpow := by zmod_pow
 heql := by decide

def Log32Mem : IdealMemCertificate B I3
 ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] ![-29, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 28
 C := ![-29, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log32Mem
 k := 14
 hpow := by zmod_pow
 heql := by decide

def Log33Mem : IdealMemCertificate B I3
 ![![29, 0, 0, 0, 0], ![18, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![26, 0, 0, 0, 1]] ![-1228505867337897533374795968991419422, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![123837635866201810568773019604025578, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R29) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1228505867337897533374795968991419416, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]
 hxeq :=  rfl
 m := 6
 C := ![-1228505867337897533374795968991419422, -72517643428740390366095921601325416, -46953523645427772413536490841175394, -54828832831176299229116821784473028, -91830583009621402898254275711388240]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log33Mem
 k := 6
 hpow := by zmod_pow
 heql := by decide

end Sat2
