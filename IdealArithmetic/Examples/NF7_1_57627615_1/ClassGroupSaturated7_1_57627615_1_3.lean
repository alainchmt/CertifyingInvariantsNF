import IdealArithmetic.Examples.NF7_1_57627615_1.ClassGroupData7_1_57627615_1
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF7_1_57627615_1.RI7_1_57627615_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat3 
instance hq43 : Fact $ Nat.Prime 43 := {out := by norm_num}
instance hq61 : Fact $ Nat.Prime 61 := {out := by norm_num}
instance hq31 : Fact $ Nat.Prime 31 := {out := by norm_num}

def R43 : IsOrderOf (3 : ZMod 43) 42 where
 m := 3
 P := ![2, 3, 7]
 e := ![1, 1, 1]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0, 0, 0], ![-11, 1, 0, 0, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![43, 0, 0, 0, 0, 0, 0], ![-12, 1, 0, 0, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0, 0, 0], ![27, 1, 0, 0, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![61, 0, 0, 0, 0, 0, 0], ![-25, 1, 0, 0, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![31, 0, 0, 0, 0, 0, 0], ![-11, 1, 0, 0, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0, 0, 0], ![20, 1, 0, 0, 0, 0, 0], ![3, 0, 1, 0, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 0], ![22, 0, 0, 0, 1, 0, 0], ![25, 0, 0, 0, 0, 1, 0], ![14, 0, 0, 0, 0, 0, 1]] where
  M :=![![![31, 0, 0, 0, 0, 0, 0], ![0, 31, 0, 0, 0, 0, 0], ![0, 0, 31, 0, 0, 0, 0], ![0, 0, 0, 31, 0, 0, 0], ![0, 0, 0, 0, 31, 0, 0], ![0, 0, 0, 0, 0, 31, 0], ![0, 0, 0, 0, 0, 0, 31]], ![![-11, 1, 0, 0, 0, 0, 0], ![0, -11, 1, 0, 0, 0, 0], ![0, 0, -11, 1, 0, 0, 0], ![0, 0, 0, -11, 1, 0, 0], ![0, 0, 0, 0, -11, 1, 0], ![-1, 1, -1, -1, 0, -11, 3], ![0, 0, 1, 0, 2, 0, -10]]]
  hmulB := by decide  
  f := ![![![-10758, 634, -46573, -60140, -351509, 31992, 135], ![-30194, -1085, -131223, -181288, -1007097, -1395, 0]], ![![-8648, 500, -37781, -48401, -281775, 25648, 108], ![-24272, -899, -106454, -145979, -807364, -1116, 0]], ![![-2172, 129, -9726, -12215, -70618, 6429, 27], ![-6096, -216, -27404, -36890, -202368, -279, 0]], ![![-2166, 121, -9846, -12391, -70788, 6446, 27], ![-6079, -237, -27744, -37417, -202895, -279, 0]], ![![-8638, 509, -37613, -48350, -281594, 25631, 108], ![-24244, -871, -105978, -145792, -806837, -1116, 0]], ![![-8612, 507, -37233, -48095, -281180, 25591, 108], ![-24171, -870, -104907, -144976, -805596, -1116, 0]], ![![-4862, 287, -21033, -27160, -158746, 14448, 61], ![-13646, -489, -59262, -81872, -454818, -630, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0, 0], ![-20, 31, 0, 0, 0, 0, 0], ![-3, 0, 31, 0, 0, 0, 0], ![-2, 0, 0, 31, 0, 0, 0], ![-22, 0, 0, 0, 31, 0, 0], ![-25, 0, 0, 0, 0, 31, 0], ![-14, 0, 0, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0, 0, 0], ![7, -11, 1, 0, 0, 0, 0], ![1, 0, -11, 1, 0, 0, 0], ![0, 0, 0, -11, 1, 0, 0], ![7, 0, 0, 0, -11, 1, 0], ![7, 1, -1, -1, 0, -11, 3], ![3, 0, 1, 0, 2, 0, -10]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 31 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![43, 0, 0, 0, 0, 0, 0], ![-12, 1, 0, 0, 0, 0, 0]] 
 ![![43, 0, 0, 0, 0, 0, 0], ![31, 1, 0, 0, 0, 0, 0], ![28, 0, 1, 0, 0, 0, 0], ![35, 0, 0, 1, 0, 0, 0], ![33, 0, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 0, 1, 0], ![32, 0, 0, 0, 0, 0, 1]] where
  M :=![![![43, 0, 0, 0, 0, 0, 0], ![0, 43, 0, 0, 0, 0, 0], ![0, 0, 43, 0, 0, 0, 0], ![0, 0, 0, 43, 0, 0, 0], ![0, 0, 0, 0, 43, 0, 0], ![0, 0, 0, 0, 0, 43, 0], ![0, 0, 0, 0, 0, 0, 43]], ![![-12, 1, 0, 0, 0, 0, 0], ![0, -12, 1, 0, 0, 0, 0], ![0, 0, -12, 1, 0, 0, 0], ![0, 0, 0, -12, 1, 0, 0], ![0, 0, 0, 0, -12, 1, 0], ![-1, 1, -1, -1, 0, -12, 3], ![0, 0, 1, 0, 2, 0, -11]]]
  hmulB := by decide  
  f := ![![![-81623, 9694, 377061, -1272456, -3560400, 301860, 864], ![-291454, 9417, 1352952, -4445856, -13128588, -12384, 0]], ![![-61235, 7269, 282796, -954342, -2670408, 226404, 648], ![-218654, 7052, 1014714, -3334392, -9846828, -9288, 0]], ![![-54428, 6464, 251302, -848226, -2373606, 201240, 576], ![-194348, 6279, 901710, -2963646, -8752392, -8256, 0]], ![![-68023, 8076, 314134, -1060445, -2966994, 251550, 720], ![-242892, 7838, 1127160, -3705138, -10940490, -10320, 0]], ![![-64617, 7674, 298402, -1007436, -2818805, 238986, 684], ![-230730, 7454, 1070712, -3519936, -10394046, -9804, 0]], ![![-17001, 2026, 78558, -265092, -741744, 62887, 180], ![-60706, 1986, 281880, -926208, -2735100, -2580, 0]], ![![-60736, 7220, 280603, -946944, -2649600, 224640, 643], ![-216872, 7031, 1006848, -3308544, -9770112, -9216, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0, 0], ![-31, 43, 0, 0, 0, 0, 0], ![-28, 0, 43, 0, 0, 0, 0], ![-35, 0, 0, 43, 0, 0, 0], ![-33, 0, 0, 0, 43, 0, 0], ![-9, 0, 0, 0, 0, 43, 0], ![-32, 0, 0, 0, 0, 0, 43]], ![![-1, 1, 0, 0, 0, 0, 0], ![8, -12, 1, 0, 0, 0, 0], ![7, 0, -12, 1, 0, 0, 0], ![9, 0, 0, -12, 1, 0, 0], ![9, 0, 0, 0, -12, 1, 0], ![1, 1, -1, -1, 0, -12, 3], ![6, 0, 1, 0, 2, 0, -11]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 43 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0, 0, 0], ![27, 1, 0, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0, 0, 0], ![27, 1, 0, 0, 0, 0, 0], ![3, 0, 1, 0, 0, 0, 0], ![41, 0, 0, 1, 0, 0, 0], ![52, 0, 0, 0, 1, 0, 0], ![60, 0, 0, 0, 0, 1, 0], ![55, 0, 0, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0, 0, 0], ![0, 61, 0, 0, 0, 0, 0], ![0, 0, 61, 0, 0, 0, 0], ![0, 0, 0, 61, 0, 0, 0], ![0, 0, 0, 0, 61, 0, 0], ![0, 0, 0, 0, 0, 61, 0], ![0, 0, 0, 0, 0, 0, 61]], ![![27, 1, 0, 0, 0, 0, 0], ![0, 27, 1, 0, 0, 0, 0], ![0, 0, 27, 1, 0, 0, 0], ![0, 0, 0, 27, 1, 0, 0], ![0, 0, 0, 0, 27, 1, 0], ![-1, 1, -1, -1, 0, 27, 3], ![0, 0, 1, 0, 2, 0, 28]]]
  hmulB := by decide  
  f := ![![![512455, 130674, -17122200, 17987924, 168280944, 6179544, -3060], ![-1155462, -254736, 38695228, -42070236, -378632124, 62220, 0]], ![![230580, 58797, -7704218, 8095507, 75726248, 2780787, -1377], ![-519902, -114619, 17411108, -18933668, -170383980, 27999, 0]], ![![25578, 6510, -856181, 900587, 8415004, 309011, -153], ![-57672, -12687, 1934920, -2106208, -18933668, 3111, 0]], ![![350160, 89289, -11700815, 12291654, 114992748, 4222717, -2091], ![-789526, -174060, 26443196, -28747836, -258733696, 42517, 0]], ![![444108, 113246, -14840058, 15589444, 145842921, 5355584, -2652], ![-1001356, -220762, 33537712, -36460736, -328146572, 53924, 0]], ![![503875, 128475, -16836815, 17688127, 165476272, 6076552, -3009], ![-1136116, -250446, 38050272, -41369068, -372321612, 61183, 0]], ![![462031, 117798, -15438050, 16218620, 151728720, 5571720, -2759], ![-1041768, -229630, 34889140, -37932180, -341389620, 56100, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0, 0], ![-27, 61, 0, 0, 0, 0, 0], ![-3, 0, 61, 0, 0, 0, 0], ![-41, 0, 0, 61, 0, 0, 0], ![-52, 0, 0, 0, 61, 0, 0], ![-60, 0, 0, 0, 0, 61, 0], ![-55, 0, 0, 0, 0, 0, 61]], ![![0, 1, 0, 0, 0, 0, 0], ![-12, 27, 1, 0, 0, 0, 0], ![-2, 0, 27, 1, 0, 0, 0], ![-19, 0, 0, 27, 1, 0, 0], ![-24, 0, 0, 0, 27, 1, 0], ![-29, 1, -1, -1, 0, 27, 3], ![-27, 0, 1, 0, 2, 0, 28]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 61 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def A3: IdealEqSpanCertificate' Table ![![61, 0, 0, 0, 0, 0, 0], ![-25, 1, 0, 0, 0, 0, 0]] 
 ![![61, 0, 0, 0, 0, 0, 0], ![36, 1, 0, 0, 0, 0, 0], ![46, 0, 1, 0, 0, 0, 0], ![52, 0, 0, 1, 0, 0, 0], ![19, 0, 0, 0, 1, 0, 0], ![48, 0, 0, 0, 0, 1, 0], ![34, 0, 0, 0, 0, 0, 1]] where
  M :=![![![61, 0, 0, 0, 0, 0, 0], ![0, 61, 0, 0, 0, 0, 0], ![0, 0, 61, 0, 0, 0, 0], ![0, 0, 0, 61, 0, 0, 0], ![0, 0, 0, 0, 61, 0, 0], ![0, 0, 0, 0, 0, 61, 0], ![0, 0, 0, 0, 0, 0, 61]], ![![-25, 1, 0, 0, 0, 0, 0], ![0, -25, 1, 0, 0, 0, 0], ![0, 0, -25, 1, 0, 0, 0], ![0, 0, 0, -25, 1, 0, 0], ![0, 0, 0, 0, -25, 1, 0], ![-1, 1, -1, -1, 0, -25, 3], ![0, 0, 1, 0, 2, 0, -24]]]
  hmulB := by decide  
  f := ![![![248359, -46205, -6094453, 10592406, 9944220, -406626, -924], ![605242, -87779, -14874728, 25249730, 25273886, 18788, 0]], ![![159624, -29700, -3917627, 6808648, 6391682, -261360, -594], ![388998, -56425, -9561750, 16230148, 16244910, 12078, 0]], ![![195128, -36312, -4788577, 8322490, 7812574, -319462, -726], ![475520, -68990, -11687478, 19838786, 19856232, 14762, 0]], ![![212896, -39609, -5223827, 9079127, 8523856, -348546, -792], ![518820, -75249, -12749792, 21642434, 21663906, 16104, 0]], ![![88689, -16497, -2176691, 3782328, 3550395, -145178, -330], ![216132, -31339, -5312648, 9016106, 9023608, 6710, 0]], ![![195160, -36310, -4788496, 8322622, 7813344, -319493, -726], ![475598, -68982, -11687280, 19839116, 19858124, 14762, 0]], ![![138446, -25760, -3396908, 5903964, 5542680, -226644, -515], ![337388, -48940, -8290832, 14073620, 14087084, 10472, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0, 0], ![-36, 61, 0, 0, 0, 0, 0], ![-46, 0, 61, 0, 0, 0, 0], ![-52, 0, 0, 61, 0, 0, 0], ![-19, 0, 0, 0, 61, 0, 0], ![-48, 0, 0, 0, 0, 61, 0], ![-34, 0, 0, 0, 0, 0, 61]], ![![-1, 1, 0, 0, 0, 0, 0], ![14, -25, 1, 0, 0, 0, 0], ![18, 0, -25, 1, 0, 0, 0], ![21, 0, 0, -25, 1, 0, 0], ![7, 0, 0, 0, -25, 1, 0], ![19, 1, -1, -1, 0, -25, 3], ![12, 0, 1, 0, 2, 0, -24]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N3 : Nat.card (O ⧸ I3) = 61 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)

def Log00Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0, 0, 0], ![20, 1, 0, 0, 0, 0, 0], ![3, 0, 1, 0, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 0], ![22, 0, 0, 0, 1, 0, 0], ![25, 0, 0, 0, 0, 1, 0], ![14, 0, 0, 0, 0, 0, 1]] ![-15, 4, 1, 6, 0, 1, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-3, 4, 1, 6, 0, 1, -3]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 4, 1, 6, 0, 1, -3]
 hxeq :=  rfl
 m := 14
 C := ![-15, 4, 1, 6, 0, 1, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 22
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0, 0, 0], ![20, 1, 0, 0, 0, 0, 0], ![3, 0, 1, 0, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 0], ![22, 0, 0, 0, 1, 0, 0], ![25, 0, 0, 0, 0, 1, 0], ![14, 0, 0, 0, 0, 0, 1]] ![0, 1, 3, 4, 1, 0, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 1, 3, 4, 1, 0, -2]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 0 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2, 1, 3, 4, 1, 0, -2]
 hxeq :=  rfl
 m := 2
 C := ![0, 1, 3, 4, 1, 0, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 24
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0, 0, 0], ![20, 1, 0, 0, 0, 0, 0], ![3, 0, 1, 0, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 0], ![22, 0, 0, 0, 1, 0, 0], ![25, 0, 0, 0, 0, 1, 0], ![14, 0, 0, 0, 0, 0, 1]] ![-4, 3, 1, 6, 0, 1, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-2, 3, 1, 6, 0, 1, -3]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 zeta3 1 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 3, 1, 6, 0, 1, -3]
 hxeq :=  rfl
 m := 3
 C := ![-4, 3, 1, 6, 0, 1, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log03Mem : IdealMemCertificate B I0
 ![![31, 0, 0, 0, 0, 0, 0], ![20, 1, 0, 0, 0, 0, 0], ![3, 0, 1, 0, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 0], ![22, 0, 0, 0, 1, 0, 0], ![25, 0, 0, 0, 0, 1, 0], ![14, 0, 0, 0, 0, 0, 1]] ![-11, 1, -1, 3, 0, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 1, -1, 3, 0, 1, -2]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 2 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 1, -1, 3, 0, 1, -2]
 hxeq :=  rfl
 m := 10
 C := ![-11, 1, -1, 3, 0, 1, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log03Mem
 k := 14
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![43, 0, 0, 0, 0, 0, 0], ![31, 1, 0, 0, 0, 0, 0], ![28, 0, 1, 0, 0, 0, 0], ![35, 0, 0, 1, 0, 0, 0], ![33, 0, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 0, 1, 0], ![32, 0, 0, 0, 0, 0, 1]] ![-26, 4, 1, 6, 0, 1, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-7, 4, 1, 6, 0, 1, -3]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 2 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 4, 1, 6, 0, 1, -3]
 hxeq :=  rfl
 m := 25
 C := ![-26, 4, 1, 6, 0, 1, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 8
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![43, 0, 0, 0, 0, 0, 0], ![31, 1, 0, 0, 0, 0, 0], ![28, 0, 1, 0, 0, 0, 0], ![35, 0, 0, 1, 0, 0, 0], ![33, 0, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 0, 1, 0], ![32, 0, 0, 0, 0, 0, 1]] ![-34, 1, 3, 4, 1, 0, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-6, 1, 3, 4, 1, 0, -2]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 2 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2, 1, 3, 4, 1, 0, -2]
 hxeq :=  rfl
 m := 36
 C := ![-34, 1, 3, 4, 1, 0, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 14
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![43, 0, 0, 0, 0, 0, 0], ![31, 1, 0, 0, 0, 0, 0], ![28, 0, 1, 0, 0, 0, 0], ![35, 0, 0, 1, 0, 0, 0], ![33, 0, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 0, 1, 0], ![32, 0, 0, 0, 0, 0, 1]] ![-14, 3, 1, 6, 0, 1, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-6, 3, 1, 6, 0, 1, -3]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 zeta3 2 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 3, 1, 6, 0, 1, -3]
 hxeq :=  rfl
 m := 13
 C := ![-14, 3, 1, 6, 0, 1, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 32
 hpow := by zmod_pow
 heql := by decide

def Log13Mem : IdealMemCertificate B I1
 ![![43, 0, 0, 0, 0, 0, 0], ![31, 1, 0, 0, 0, 0, 0], ![28, 0, 1, 0, 0, 0, 0], ![35, 0, 0, 1, 0, 0, 0], ![33, 0, 0, 0, 1, 0, 0], ![9, 0, 0, 0, 0, 1, 0], ![32, 0, 0, 0, 0, 0, 1]] ![-33, 1, -1, 3, 0, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-2, 1, -1, 3, 0, 1, -2]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R43) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 1, -1, 3, 0, 1, -2]
 hxeq :=  rfl
 m := 32
 C := ![-33, 1, -1, 3, 0, 1, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log13Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0, 0, 0], ![27, 1, 0, 0, 0, 0, 0], ![3, 0, 1, 0, 0, 0, 0], ![41, 0, 0, 1, 0, 0, 0], ![52, 0, 0, 0, 1, 0, 0], ![60, 0, 0, 0, 0, 1, 0], ![55, 0, 0, 0, 0, 0, 1]] ![-53, 4, 1, 6, 0, 1, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-5, 4, 1, 6, 0, 1, -3]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 0 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 4, 1, 6, 0, 1, -3]
 hxeq :=  rfl
 m := 52
 C := ![-53, 4, 1, 6, 0, 1, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 42
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0, 0, 0], ![27, 1, 0, 0, 0, 0, 0], ![3, 0, 1, 0, 0, 0, 0], ![41, 0, 0, 1, 0, 0, 0], ![52, 0, 0, 0, 1, 0, 0], ![60, 0, 0, 0, 0, 1, 0], ![55, 0, 0, 0, 0, 0, 1]] ![-41, 1, 3, 4, 1, 0, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-3, 1, 3, 4, 1, 0, -2]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 1 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2, 1, 3, 4, 1, 0, -2]
 hxeq :=  rfl
 m := 43
 C := ![-41, 1, 3, 4, 1, 0, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 43
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0, 0, 0], ![27, 1, 0, 0, 0, 0, 0], ![3, 0, 1, 0, 0, 0, 0], ![41, 0, 0, 1, 0, 0, 0], ![52, 0, 0, 0, 1, 0, 0], ![60, 0, 0, 0, 0, 1, 0], ![55, 0, 0, 0, 0, 0, 1]] ![-19, 3, 1, 6, 0, 1, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-4, 3, 1, 6, 0, 1, -3]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 zeta3 1 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 3, 1, 6, 0, 1, -3]
 hxeq :=  rfl
 m := 18
 C := ![-19, 3, 1, 6, 0, 1, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 13
 hpow := by zmod_pow
 heql := by decide

def Log23Mem : IdealMemCertificate B I2
 ![![61, 0, 0, 0, 0, 0, 0], ![27, 1, 0, 0, 0, 0, 0], ![3, 0, 1, 0, 0, 0, 0], ![41, 0, 0, 1, 0, 0, 0], ![52, 0, 0, 0, 1, 0, 0], ![60, 0, 0, 0, 0, 1, 0], ![55, 0, 0, 0, 0, 0, 1]] ![-25, 1, -1, 3, 0, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-2, 1, -1, 3, 0, 1, -2]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 0 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 1, -1, 3, 0, 1, -2]
 hxeq :=  rfl
 m := 24
 C := ![-25, 1, -1, 3, 0, 1, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log23Mem
 k := 9
 hpow := by zmod_pow
 heql := by decide

def Log30Mem : IdealMemCertificate B I3
 ![![61, 0, 0, 0, 0, 0, 0], ![36, 1, 0, 0, 0, 0, 0], ![46, 0, 1, 0, 0, 0, 0], ![52, 0, 0, 1, 0, 0, 0], ![19, 0, 0, 0, 1, 0, 0], ![48, 0, 0, 0, 0, 1, 0], ![34, 0, 0, 0, 0, 0, 1]] ![-40, 4, 1, 6, 0, 1, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-8, 4, 1, 6, 0, 1, -3]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 zeta1 1 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 4, 1, 6, 0, 1, -3]
 hxeq :=  rfl
 m := 39
 C := ![-40, 4, 1, 6, 0, 1, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log30Mem
 k := 46
 hpow := by zmod_pow
 heql := by decide

def Log31Mem : IdealMemCertificate B I3
 ![![61, 0, 0, 0, 0, 0, 0], ![36, 1, 0, 0, 0, 0, 0], ![46, 0, 1, 0, 0, 0, 0], ![52, 0, 0, 1, 0, 0, 0], ![19, 0, 0, 0, 1, 0, 0], ![48, 0, 0, 0, 0, 1, 0], ![34, 0, 0, 0, 0, 0, 1]] ![-33, 1, 3, 4, 1, 0, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-6, 1, 3, 4, 1, 0, -2]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 zeta2 2 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2, 1, 3, 4, 1, 0, -2]
 hxeq :=  rfl
 m := 35
 C := ![-33, 1, 3, 4, 1, 0, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log31Mem
 k := 11
 hpow := by zmod_pow
 heql := by decide

def Log32Mem : IdealMemCertificate B I3
 ![![61, 0, 0, 0, 0, 0, 0], ![36, 1, 0, 0, 0, 0, 0], ![46, 0, 1, 0, 0, 0, 0], ![52, 0, 0, 1, 0, 0, 0], ![19, 0, 0, 0, 1, 0, 0], ![48, 0, 0, 0, 0, 1, 0], ![34, 0, 0, 0, 0, 0, 1]] ![-15, 3, 1, 6, 0, 1, -3] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-7, 3, 1, 6, 0, 1, -3]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 zeta3 2 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 3, 1, 6, 0, 1, -3]
 hxeq :=  rfl
 m := 14
 C := ![-15, 3, 1, 6, 0, 1, -3]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log32Mem
 k := 50
 hpow := by zmod_pow
 heql := by decide

def Log33Mem : IdealMemCertificate B I3
 ![![61, 0, 0, 0, 0, 0, 0], ![36, 1, 0, 0, 0, 0, 0], ![46, 0, 1, 0, 0, 0, 0], ![52, 0, 0, 1, 0, 0, 0], ![19, 0, 0, 0, 1, 0, 0], ![48, 0, 0, 0, 0, 1, 0], ![34, 0, 0, 0, 0, 0, 1]] ![-57, 1, -1, 3, 0, 1, -2] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-3, 1, -1, 3, 0, 1, -2]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R61) ▸ IsPrimitiveRoot.orderOf _) 3 alpha0 1 where
 r := 7
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, 1, -1, 3, 0, 1, -2]
 hxeq :=  rfl
 m := 56
 C := ![-57, 1, -1, 3, 0, 1, -2]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log33Mem
 k := 52
 hpow := by zmod_pow
 heql := by decide

end Sat3
