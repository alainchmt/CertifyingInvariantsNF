import IdealArithmetic.Examples.NF5_1_337500000_4.ClassGroupData5_1_337500000_4
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_337500000_4.RI5_1_337500000_4

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat5 
instance hq101 : Fact $ Nat.Prime 101 := {out := by norm_num}
instance hq61 : Fact $ Nat.Prime 61 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

def R101 : IsOrderOf (2 : ZMod 101) 100 where
 m := 2
 P := ![2, 5]
 e := ![2, 2]
 hP := fun i => by fin_cases i <;> norm_num
 hm := by rfl
 hid := by zmod_pow
 hnid := fun i => by fin_cases i ; repeat zmod_pow

def R61 : IsOrderOf (2 : ZMod 61) 60 where
 m := 3
 P := ![2, 3, 5]
 e := ![2, 1, 1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![10, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0], ![10, 1, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0], ![10, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![10, 1, 0, 0, 0], ![0, 10, 1, 0, 0], ![1, -1, 12, 7, 0], ![-2, -1, 0, 8, 6], ![-10, -5, 1, 2, 10]]]
  hmulB := by decide  
  f := ![![![46671279, 5221624, 4467174, 2548014, -1596], ![-143549964, -2960562, -11293486, 8246, 0]], ![![17194422, 1923723, 1645776, 938728, -588], ![-52886030, -1090704, -4160696, 3038, 0]], ![![36844847, 4122229, 3526630, 2011541, -1260], ![-113326152, -2337213, -8915693, 6510, 0]], ![![27020302, 3023052, 2586267, 1475171, -924], ![-83108144, -1714005, -6538356, 4774, 0]], ![![43660241, 4884744, 4178969, 2383626, -1493], ![-134288714, -2769551, -10564874, 7714, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-10, 31, 0, 0, 0], ![-24, 0, 31, 0, 0], ![-18, 0, 0, 31, 0], ![-29, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![-4, 10, 1, 0, 0], ![-13, -1, 12, 7, 0], ![-10, -1, 0, 8, 6], ![-10, -5, 1, 2, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0], ![0, 61, 0, 0, 0], ![0, 0, 61, 0, 0], ![0, 0, 0, 61, 0], ![0, 0, 0, 0, 61]], ![![-11, 1, 0, 0, 0], ![0, -11, 1, 0, 0], ![1, -1, -9, 7, 0], ![-2, -1, 0, -13, 6], ![-10, -5, 1, 2, -11]]]
  hmulB := by decide  
  f := ![![![20960568, -1986780, -272910, 247111, -14256], ![116038226, -310551, -1884229, 144936, 0]], ![![17467221, -1655663, -227426, 205927, -11880], ![96698970, -258823, -1570201, 120780, 0]], ![![388159, -36789, -5054, 4576, -264], ![2148858, -5733, -34892, 2684, 0]], ![![8927660, -846216, -116240, 105251, -6072], ![49423748, -132238, -802542, 61732, 0]], ![![15119104, -1433089, -196853, 178244, -10283], ![83699736, -224011, -1359116, 104544, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-50, 61, 0, 0, 0], ![-1, 0, 61, 0, 0], ![-26, 0, 0, 61, 0], ![-44, 0, 0, 0, 61]], ![![-1, 1, 0, 0, 0], ![9, -11, 1, 0, 0], ![-2, -1, -9, 7, 0], ![2, -1, 0, -13, 6], ![11, -5, 1, 2, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 61 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0], ![10, 1, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] where
  M :=![![![101, 0, 0, 0, 0], ![0, 101, 0, 0, 0], ![0, 0, 101, 0, 0], ![0, 0, 0, 101, 0], ![0, 0, 0, 0, 101]], ![![10, 1, 0, 0, 0], ![0, 10, 1, 0, 0], ![1, -1, 12, 7, 0], ![-2, -1, 0, 8, 6], ![-10, -5, 1, 2, 10]]]
  hmulB := by decide  
  f := ![![![-46445053581, -4630919069, -750289018, -434531492, -40044], ![468468286163, 552411218, 6268898300, 674074, 0]], ![![-4941030050, -492657637, -79819061, -46227380, -4260], ![49837726538, 58767961, 666913100, 71710, 0]], ![![-494095527, -49265026, -7981786, -4622668, -426], ![4983697227, 5876787, 66690300, 7171, 0]], ![![-33104453094, -3300761461, -534780470, -309719255, -28542], ![333908246618, 393739870, 4468257300, 480457, 0]], ![![-18394080640, -1834027360, -297144166, -172091680, -15859], ![185531994660, 218776766, 2482732000, 266960, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-10, 101, 0, 0, 0], ![-1, 0, 101, 0, 0], ![-72, 0, 0, 101, 0], ![-40, 0, 0, 0, 101]], ![![0, 1, 0, 0, 0], ![-1, 10, 1, 0, 0], ![-5, -1, 12, 7, 0], ![-8, -1, 0, 8, 6], ![-5, -5, 1, 2, 10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 101 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def Log00Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] ![-48, -3, 3, -2, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![2, -3, 3, -2, -4]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-31, -3, 3, -2, -4]
 hxeq :=  rfl
 m := 17
 C := ![-48, -3, 3, -2, -4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 7
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] ![392694878105, 289411646068, 23958228906, -45790090041, -121311276284] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![40833211505, 289411646068, 23958228906, -45790090041, -121311276284]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![392694878126, 289411646068, 23958228906, -45790090041, -121311276284]
 hxeq :=  rfl
 m := 21
 C := ![392694878105, 289411646068, 23958228906, -45790090041, -121311276284]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 29
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![24, 0, 1, 0, 0], ![18, 0, 0, 1, 0], ![29, 0, 0, 0, 1]] ![6757387, 6027576, -1809813, -4094779, 6741089] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-4253820, 6027576, -1809813, -4094779, 6741089]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![6757389, 6027576, -1809813, -4094779, 6741089]
 hxeq :=  rfl
 m := 2
 C := ![6757387, 6027576, -1809813, -4094779, 6741089]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 24
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![61, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] ![-70, -3, 3, -2, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![5, -3, 3, -2, -4]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-31, -3, 3, -2, -4]
 hxeq :=  rfl
 m := 39
 C := ![-70, -3, 3, -2, -4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 46
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![61, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] ![392694878113, 289411646068, 23958228906, -45790090041, -121311276284] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-124157494371, 289411646068, 23958228906, -45790090041, -121311276284]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![392694878126, 289411646068, 23958228906, -45790090041, -121311276284]
 hxeq :=  rfl
 m := 13
 C := ![392694878113, 289411646068, 23958228906, -45790090041, -121311276284]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 40
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![61, 0, 0, 0, 0], ![50, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![26, 0, 0, 1, 0], ![44, 0, 0, 0, 1]] ![6757349, 6027576, -1809813, -4094779, 6741089] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-7917300, 6027576, -1809813, -4094779, 6741089]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![6757389, 6027576, -1809813, -4094779, 6741089]
 hxeq :=  rfl
 m := 40
 C := ![6757349, 6027576, -1809813, -4094779, 6741089]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 25
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![101, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] ![-129, -3, 3, -2, -4] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![2, -3, 3, -2, -4]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 5 zeta1 4 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-31, -3, 3, -2, -4]
 hxeq :=  rfl
 m := 98
 C := ![-129, -3, 3, -2, -4]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 19
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![101, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] ![392694878105, 289411646068, 23958228906, -45790090041, -121311276284] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![55682749731, 289411646068, 23958228906, -45790090041, -121311276284]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 5 zeta2 3 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![392694878126, 289411646068, 23958228906, -45790090041, -121311276284]
 hxeq :=  rfl
 m := 21
 C := ![392694878105, 289411646068, 23958228906, -45790090041, -121311276284]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 78
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![101, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![72, 0, 0, 1, 0], ![40, 0, 0, 0, 1]] ![6757365, 6027576, -1809813, -4094779, 6741089] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-262654, 6027576, -1809813, -4094779, 6741089]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 5 alpha0 2 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![6757389, 6027576, -1809813, -4094779, 6741089]
 hxeq :=  rfl
 m := 24
 C := ![6757365, 6027576, -1809813, -4094779, 6741089]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 72
 hpow := by zmod_pow
 heql := by decide

end Sat5
