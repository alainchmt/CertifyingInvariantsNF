import IdealArithmetic.Examples.NF5_1_3037500000_7.ClassGroupData5_1_3037500000_7
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_3037500000_7.RI5_1_3037500000_7

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq11 : Fact $ Nat.Prime 11 := {out := by norm_num}
instance hq131 : Fact $ Nat.Prime 131 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

def R11 : IsOrderOf (2 : ZMod 11) 10 where
 m := 2
 P := ![2, 5]
 e := ![1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R131 : IsOrderOf (2 : ZMod 131) 130 where
 m := 3
 P := ![2, 5, 13]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![131, 0, 0, 0, 0], ![-45, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0]] 
 ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![11, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![0, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 5, 0], ![98, -82, 57, 68, 222], ![-32, 24, -17, -22, -68]]]
  hmulB := by decide  
  f := ![![![99, -246, 112, 53, 222], ![1804, -605, 33, -11, 0]], ![![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0], ![0, 1, 0, 0, 0]], ![![0, 0, 0, -4, 0], ![0, 0, 9, 0, 0]], ![![45, -111, 50, 25, 101], ![811, -265, 13, -5, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![0, 11, 0, 0, 0], ![0, 0, 11, 0, 0], ![0, 0, 0, 11, 0], ![-5, 0, 0, 0, 11]], ![![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 5, 0], ![-92, -82, 57, 68, 222], ![28, 24, -17, -22, -68]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 11 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![7, 1, 0, 0, 0], ![0, 7, 1, 0, 0], ![0, 0, 7, 5, 0], ![98, -82, 57, 75, 222], ![-32, 24, -17, -22, -61]]]
  hmulB := by decide  
  f := ![![![2830668, 291689, 12551136, 8989380, 115884], ![-12309263, 277140, -55491426, -16182, 0]], ![![786282, 81018, 3486405, 2497035, 32190], ![-3419175, 77004, -15414192, -4495, 0]], ![![1258070, 129641, 5578262, 3995265, 51504], ![-5470763, 123164, -24662763, -7192, 0]], ![![1729844, 178253, 7670140, 5493511, 70818], ![-7522289, 169364, -33911433, -9889, 0]], ![![456558, 47041, 2024376, 1449900, 18691], ![-1985359, 44724, -8950230, -2610, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-7, 31, 0, 0, 0], ![-13, 0, 31, 0, 0], ![-19, 0, 0, 31, 0], ![-5, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![-2, 7, 1, 0, 0], ![-6, 0, 7, 5, 0], ![-84, -82, 57, 75, 222], ![24, 24, -17, -22, -61]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![131, 0, 0, 0, 0], ![-45, 1, 0, 0, 0]] 
 ![![131, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![113, 0, 0, 0, 1]] where
  M :=![![![131, 0, 0, 0, 0], ![0, 131, 0, 0, 0], ![0, 0, 131, 0, 0], ![0, 0, 0, 131, 0], ![0, 0, 0, 0, 131]], ![![-45, 1, 0, 0, 0], ![0, -45, 1, 0, 0], ![0, 0, -45, 5, 0], ![98, -82, 57, 23, 222], ![-32, 24, -17, -22, -113]]]
  hmulB := by decide  
  f := ![![![4489873156, -140159570, -13057846029, 1451231100, 1978020], ![13067977705, -115493661, -38016885654, -1167210, 0]], ![![2993248756, -93439713, -8705230686, 967487400, 1318680], ![8711985094, -76995774, -25344590436, -778140, 0]], ![![2444486524, -76309095, -7109272024, 790114743, 1076922], ![7114787943, -62879868, -20698083054, -635481, 0]], ![![3941110868, -123028948, -11461887061, 1273858409, 1736262], ![11470780391, -101377747, -33370377381, -1024551, 0]], ![![3872944018, -120901034, -11263638177, 1251825300, 1706231], ![11272377709, -99624393, -32793191442, -1006830, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-86, 131, 0, 0, 0], ![-71, 0, 131, 0, 0], ![-115, 0, 0, 131, 0], ![-113, 0, 0, 0, 131]], ![![-1, 1, 0, 0, 0], ![29, -45, 1, 0, 0], ![20, 0, -45, 5, 0], ![-188, -82, 57, 23, 222], ![110, 24, -17, -22, -113]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 131 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-416359, 88799, -67875, -113988, -357834] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![124801, 88799, -67875, -113988, -357834]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-416355, 88799, -67875, -113988, -357834]
 hxeq :=  rfl
 m := 4
 C := ![-416359, 88799, -67875, -113988, -357834]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![27871707746025725, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-20765475697636235, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![27871707746025729, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862]
 hxeq :=  rfl
 m := 4
 C := ![27871707746025725, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![11, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-15497, 74713, -35713, -46552, -141563] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![62938, 74713, -35713, -46552, -141563]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R11) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-15494, 74713, -35713, -46552, -141563]
 hxeq :=  rfl
 m := 3
 C := ![-15497, 74713, -35713, -46552, -141563]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-416364, 88799, -67875, -113988, -357834] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![122560, 88799, -67875, -113988, -357834]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-416355, 88799, -67875, -113988, -357834]
 hxeq :=  rfl
 m := 9
 C := ![-416364, 88799, -67875, -113988, -357834]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![27871707746025723, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-18131959490855753, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![27871707746025729, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862]
 hxeq :=  rfl
 m := 6
 C := ![27871707746025723, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 25
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![31, 0, 0, 0, 0], ![7, 1, 0, 0, 0], ![13, 0, 1, 0, 0], ![19, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-15511, 74713, -35713, -46552, -141563] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![48970, 74713, -35713, -46552, -141563]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-15494, 74713, -35713, -46552, -141563]
 hxeq :=  rfl
 m := 17
 C := ![-15511, 74713, -35713, -46552, -141563]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![131, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![113, 0, 0, 0, 1]] ![-416378, 88799, -67875, -113988, -357834] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![384045, 88799, -67875, -113988, -357834]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R131) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-416355, 88799, -67875, -113988, -357834]
 hxeq :=  rfl
 m := 23
 C := ![-416378, 88799, -67875, -113988, -357834]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 23
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![131, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![113, 0, 0, 0, 1]] ![27871707746025652, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-53667031026502929, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R131) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![27871707746025729, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862]
 hxeq :=  rfl
 m := 77
 C := ![27871707746025652, -14999638523133007, 12892911205012467, 14266322923120986, 51258388084004862]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 22
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![131, 0, 0, 0, 0], ![86, 1, 0, 0, 0], ![71, 0, 1, 0, 0], ![115, 0, 0, 1, 0], ![113, 0, 0, 0, 1]] ![-15527, 74713, -35713, -46552, -141563] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![133167, 74713, -35713, -46552, -141563]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R131) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-15494, 74713, -35713, -46552, -141563]
 hxeq :=  rfl
 m := 33
 C := ![-15527, 74713, -35713, -46552, -141563]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 128
 hpow := by zmod_pow
 heql := by decide

end Sat5
