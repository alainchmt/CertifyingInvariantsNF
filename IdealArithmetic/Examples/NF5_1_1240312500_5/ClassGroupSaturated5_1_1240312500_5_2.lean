import IdealArithmetic.Examples.NF5_1_1240312500_5.ClassGroupData5_1_1240312500_5
import IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.PrincipalityCertificate
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF5_1_1240312500_5.RI5_1_1240312500_5

open BigOperators Classical Matrix Polynomial

noncomputable section 

namespace Sat2 
instance hq17 : Fact $ Nat.Prime 17 := by decide
instance hq3 : Fact $ Nat.Prime 3 := by decide
instance hq7 : Fact $ Nat.Prime 7 := by decide
instance hq31 : Fact $ Nat.Prime 31 := by decide

def R17 : IsOrderOf (3 : ZMod 17) 16 where
 m := 1
 P := ![2]
 e := ![4]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def R3 : IsOrderOf (2 : ZMod 3) 2 where
 m := 1
 P := ![2]
 e := ![1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def R7 : IsOrderOf (3 : ZMod 7) 6 where
 m := 2
 P := ![2, 3]
 e := ![1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def R31 : IsOrderOf (3 : ZMod 31) 30 where
 m := 3
 P := ![2, 3, 5]
 e := ![1, 1, 1]
 hP := by decide
 hm := by rfl
 hid := by decide
 hnid := by decide

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0, 0, 0], ![-7, 1, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![12, 1, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![31, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] i)))
def I4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0, 0, 0], ![-23, -15, -8, -10, 26]] i)))

def A0: IdealEqSpanCertificate O ℤ timesTableO I0
 ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]] 
 ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![3, 0, 0, 0, 0], ![0, 3, 0, 0, 0], ![0, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![0, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![15, -70, -41, -52, 126], ![3, -27, -16, -20, 50]]]
  hmulB := by decide
  f := ![![![-15, -6, 102, -20, -100], ![-30, -120, 90, 0, 6]], ![![-15, -5, 101, -22, -100], ![-29, -114, 93, 0, 6]], ![![-6, -3, 50, -10, -50], ![-11, -56, 45, 0, 3]], ![![0, 0, 0, -1, 0], ![0, 2, 2, 0, 0]], ![![-3, -4, 34, -8, -33], ![-4, -38, 32, 0, 2]]]
  g := ![![![1, 0, 0, 0, 0], ![-2, 3, 0, 0, 0], ![-2, 0, 3, 0, 0], ![0, 0, 0, 3, 0], ![-1, 0, 0, 0, 3]], ![![-1, 1, 0, 0, 0], ![0, -1, 1, 0, 0], ![0, 1, -1, 2, 0], ![37, -70, -41, -52, 126], ![13, -27, -16, -20, 50]]]
  hle1 := by decide
  hle2 := by decide

lemma N0 : Nat.card (O ⧸ I0) = 3 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A0)

def A1: IdealEqSpanCertificate O ℤ timesTableO I1
 ![![17, 0, 0, 0, 0], ![-7, 1, 0, 0, 0]] 
 ![![17, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![17, 0, 0, 0, 0], ![0, 17, 0, 0, 0], ![0, 0, 17, 0, 0], ![0, 0, 0, 17, 0], ![0, 0, 0, 0, 17]], ![![-7, 1, 0, 0, 0], ![0, -7, 1, 0, 0], ![0, 1, -7, 2, 0], ![15, -70, -41, -58, 126], ![3, -27, -16, -20, 44]]]
  hmulB := by decide
  f := ![![![-225566, 136112, -997445, 288558, -3402], ![-546822, -100640, -2439432, 459, 0]], ![![-150384, 90747, -664964, 192372, -2268], ![-364564, -67082, -1626288, 306, 0]], ![![-50116, 30242, -221599, 64108, -756], ![-121492, -22354, -541960, 102, 0]], ![![-25060, 15127, -110831, 32063, -378], ![-60751, -11174, -271056, 51, 0]], ![![-119414, 72065, -528060, 152766, -1801], ![-289486, -53265, -1291464, 243, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-10, 17, 0, 0, 0], ![-2, 0, 17, 0, 0], ![-2, 0, 0, 17, 0], ![-9, 0, 0, 0, 17]], ![![-1, 1, 0, 0, 0], ![4, -7, 1, 0, 0], ![0, 1, -7, 2, 0], ![-13, -70, -41, -58, 126], ![-3, -27, -16, -20, 44]]]
  hle1 := by decide
  hle2 := by decide

lemma N1 : Nat.card (O ⧸ I1) = 17 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A1)

def A2: IdealEqSpanCertificate O ℤ timesTableO I2
 ![![31, 0, 0, 0, 0], ![12, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![12, 1, 0, 0, 0], ![0, 12, 1, 0, 0], ![0, 1, 12, 2, 0], ![15, -70, -41, -39, 126], ![3, -27, -16, -20, 63]]]
  hmulB := by decide
  f := ![![![-147833, -29888, -307501, -49972, -5292], ![380277, -13547, 799955, 1302, 0]], ![![-98568, -19926, -204949, -33306, -3528], ![253550, -9021, 533169, 868, 0]], ![![-98563, -19925, -204937, -33304, -3528], ![253537, -9020, 533138, 868, 0]], ![![-98565, -19928, -205003, -33315, -3528], ![253543, -9027, 533309, 868, 0]], ![![-114456, -23136, -238065, -38688, -4097], ![294420, -10497, 619320, 1008, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-12, 31, 0, 0, 0], ![-11, 0, 31, 0, 0], ![-21, 0, 0, 31, 0], ![-24, 0, 0, 0, 31]], ![![0, 1, 0, 0, 0], ![-5, 12, 1, 0, 0], ![-6, 1, 12, 2, 0], ![-29, -70, -41, -39, 126], ![-19, -27, -16, -20, 63]]]
  hle1 := by decide
  hle2 := by decide

lemma N2 : Nat.card (O ⧸ I2) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A2)

def A3: IdealEqSpanCertificate O ℤ timesTableO I3
 ![![31, 0, 0, 0, 0], ![-11, 1, 0, 0, 0]] 
 ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![31, 0, 0, 0, 0], ![0, 31, 0, 0, 0], ![0, 0, 31, 0, 0], ![0, 0, 0, 31, 0], ![0, 0, 0, 0, 31]], ![![-11, 1, 0, 0, 0], ![0, -11, 1, 0, 0], ![0, 1, -11, 2, 0], ![15, -70, -41, -62, 126], ![3, -27, -16, -20, 40]]]
  hmulB := by decide
  f := ![![![4556658, -1758189, 19755478, -3558738, -72576], ![12865837, 1166003, 55713975, 17856, 0]], ![![3037754, -1172117, 13170318, -2372492, -48384], ![8577174, 777356, 37142650, 11904, 0]], ![![569582, -219766, 2469400, -444836, -9072], ![1608229, 145763, 6964150, 2232, 0]], ![![3227638, -1245383, 13993465, -2520773, -51408], ![9113316, 825923, 39464070, 12648, 0]], ![![3674710, -1417892, 15931837, -2869950, -58529], ![10375635, 940328, 44930625, 14400, 0]]]
  g := ![![![1, 0, 0, 0, 0], ![-20, 31, 0, 0, 0], ![-3, 0, 31, 0, 0], ![-22, 0, 0, 31, 0], ![-25, 0, 0, 0, 31]], ![![-1, 1, 0, 0, 0], ![7, -11, 1, 0, 0], ![-1, 1, -11, 2, 0], ![-8, -70, -41, -62, 126], ![1, -27, -16, -20, 40]]]
  hle1 := by decide
  hle2 := by decide

lemma N3 : Nat.card (O ⧸ I3) = 31 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A3)

def A4: IdealEqSpanCertificate O ℤ timesTableO I4
 ![![7, 0, 0, 0, 0], ![-23, -15, -8, -10, 26]] 
 ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] where
  T := Table 
  heq := timesTableT_eq_Table
  hieq := rfl 
  M :=![![![7, 0, 0, 0, 0], ![0, 7, 0, 0, 0], ![0, 0, 7, 0, 0], ![0, 0, 0, 7, 0], ![0, 0, 0, 0, 7]], ![![-23, -15, -8, -10, 26], ![-72, -33, -21, -26, 66], ![-192, -55, -23, -36, 90], ![-99, -46, 1, 8, -6], ![-139, -57, -20, -24, 66]]]
  hmulB := by decide
  f := ![![![2352581409, -1227601482, 14872982, -29705584, 393247372], ![-3613263752, 1380378860, 967890, 0, 168]], ![![2100500882, -1096063220, 13279338, -26522606, 351110658], ![-3226100319, 1232470418, 864180, 0, 150]], ![![1344244743, -701440890, 8498299, -16973508, 224698140], ![-2064587742, 788736576, 553044, 0, 96]], ![![1260329711, -657653157, 7967788, -15913931, 210671270], ![-1935705007, 739499372, 518520, 0, 90]], ![![1680415302, -876858195, 10623562, -21218270, 280890969], ![-2580902677, 985984900, 691350, 0, 120]]]
  g := ![![![1, 0, 0, 0, 0], ![-5, 7, 0, 0, 0], ![-3, 0, 7, 0, 0], ![-4, 0, 0, 7, 0], ![-5, 0, 0, 0, 7]], ![![-2, -15, -8, -10, 26], ![-10, -33, -21, -26, 66], ![-22, -55, -23, -36, 90], ![18, -46, 1, 8, -6], ![-4, -57, -20, -24, 66]]]
  hle1 := by decide
  hle2 := by decide

lemma N4 : Nat.card (O ⧸ I4) = 7 := 
 ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate O ℤ A4)

def Log00Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![72621, -21683, 6662, 13571, -23580] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![42081, -21683, 6662, 13571, -23580]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![72622, -21683, 6662, 13571, -23580]
 hxeq :=  rfl
 m:= 1
 C := ![72621, -21683, 6662, 13571, -23580]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log00Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log01Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![-924606, -3154467, -3847477, -4269764, 10021778] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![1019168, -3154467, -3847477, -4269764, 10021778]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-924605, -3154467, -3847477, -4269764, 10021778]
 hxeq :=  rfl
 m:= 1
 C := ![-924606, -3154467, -3847477, -4269764, 10021778]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log01Mem
 k :=  0
 hpow := by decide
 heql := by decide

def Log02Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![-3, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 2
 C := ![-3, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log02Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log03Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![33935, 20880, 13147, 17954, -47580] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![4487, 20880, 13147, 17954, -47580]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![33937, 20880, 13147, 17954, -47580]
 hxeq :=  rfl
 m:= 2
 C := ![33935, 20880, 13147, 17954, -47580]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log03Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log04Mem : IdealMemCertificate O ℤ B I0
  ![![3, 0, 0, 0, 0], ![2, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1]] ![192, 109, 64, 85, -223] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A0
 g := ![23, 109, 64, 85, -223]
 hmem := by decide

def Log04: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R3) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![194, 109, 64, 85, -223]
 hxeq :=  rfl
 m:= 2
 C := ![192, 109, 64, 85, -223]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log04Mem
 k :=  1
 hpow := by decide
 heql := by decide

def Log10Mem : IdealMemCertificate O ℤ B I1
  ![![17, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![72609, -21683, 6662, 13571, -23580] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![27129, -21683, 6662, 13571, -23580]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![72622, -21683, 6662, 13571, -23580]
 hxeq :=  rfl
 m:= 13
 C := ![72609, -21683, 6662, 13571, -23580]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log10Mem
 k :=  4
 hpow := by decide
 heql := by decide

def Log11Mem : IdealMemCertificate O ℤ B I1
  ![![17, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![-924616, -3154467, -3847477, -4269764, 10021778] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-2549498, -3154467, -3847477, -4269764, 10021778]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-924605, -3154467, -3847477, -4269764, 10021778]
 hxeq :=  rfl
 m:= 11
 C := ![-924616, -3154467, -3847477, -4269764, 10021778]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log11Mem
 k :=  7
 hpow := by decide
 heql := by decide

def Log12Mem : IdealMemCertificate O ℤ B I1
  ![![17, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![-17, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 v 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 16
 C := ![-17, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log12Mem
 k :=  8
 hpow := by decide
 heql := by decide

def Log13Mem : IdealMemCertificate O ℤ B I1
  ![![17, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![33930, 20880, 13147, 17954, -47580] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![11244, 20880, 13147, 17954, -47580]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![33937, 20880, 13147, 17954, -47580]
 hxeq :=  rfl
 m:= 7
 C := ![33930, 20880, 13147, 17954, -47580]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log13Mem
 k :=  11
 hpow := by decide
 heql := by decide

def Log14Mem : IdealMemCertificate O ℤ B I1
  ![![17, 0, 0, 0, 0], ![10, 1, 0, 0, 0], ![2, 0, 1, 0, 0], ![2, 0, 0, 1, 0], ![9, 0, 0, 0, 1]] ![180, 109, 64, 85, -223] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A1
 g := ![47, 109, 64, 85, -223]
 hmem := by decide

def Log14: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R17) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![194, 109, 64, 85, -223]
 hxeq :=  rfl
 m:= 14
 C := ![180, 109, 64, 85, -223]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log14Mem
 k :=  9
 hpow := by decide
 heql := by decide

def Log20Mem : IdealMemCertificate O ℤ B I2
  ![![31, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] ![72611, -21683, 6662, 13571, -23580] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![17434, -21683, 6662, 13571, -23580]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![72622, -21683, 6662, 13571, -23580]
 hxeq :=  rfl
 m:= 11
 C := ![72611, -21683, 6662, 13571, -23580]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log20Mem
 k :=  23
 hpow := by decide
 heql := by decide

def Log21Mem : IdealMemCertificate O ℤ B I2
  ![![31, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] ![-924627, -3154467, -3847477, -4269764, 10021778] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-2309884, -3154467, -3847477, -4269764, 10021778]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-924605, -3154467, -3847477, -4269764, 10021778]
 hxeq :=  rfl
 m:= 22
 C := ![-924627, -3154467, -3847477, -4269764, 10021778]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log21Mem
 k :=  17
 hpow := by decide
 heql := by decide

def Log22Mem : IdealMemCertificate O ℤ B I2
  ![![31, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] ![-31, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 30
 C := ![-31, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log22Mem
 k :=  15
 hpow := by decide
 heql := by decide

def Log23Mem : IdealMemCertificate O ℤ B I2
  ![![31, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] ![33911, 20880, 13147, 17954, -47580] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![13020, 20880, 13147, 17954, -47580]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![33937, 20880, 13147, 17954, -47580]
 hxeq :=  rfl
 m:= 26
 C := ![33911, 20880, 13147, 17954, -47580]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log23Mem
 k :=  5
 hpow := by decide
 heql := by decide

def Log24Mem : IdealMemCertificate O ℤ B I2
  ![![31, 0, 0, 0, 0], ![12, 1, 0, 0, 0], ![11, 0, 1, 0, 0], ![21, 0, 0, 1, 0], ![24, 0, 0, 0, 1]] ![181, 109, 64, 85, -223] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A2
 g := ![56, 109, 64, 85, -223]
 hmem := by decide

def Log24: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![194, 109, 64, 85, -223]
 hxeq :=  rfl
 m:= 13
 C := ![181, 109, 64, 85, -223]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log24Mem
 k :=  11
 hpow := by decide
 heql := by decide

def Log30Mem : IdealMemCertificate O ℤ B I3
  ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] ![72620, -21683, 6662, 13571, -23580] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![25072, -21683, 6662, 13571, -23580]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![72622, -21683, 6662, 13571, -23580]
 hxeq :=  rfl
 m:= 2
 C := ![72620, -21683, 6662, 13571, -23580]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log30Mem
 k :=  24
 hpow := by decide
 heql := by decide

def Log31Mem : IdealMemCertificate O ℤ B I3
  ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] ![-924623, -3154467, -3847477, -4269764, 10021778] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-2674274, -3154467, -3847477, -4269764, 10021778]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-924605, -3154467, -3847477, -4269764, 10021778]
 hxeq :=  rfl
 m:= 18
 C := ![-924623, -3154467, -3847477, -4269764, 10021778]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log31Mem
 k :=  26
 hpow := by decide
 heql := by decide

def Log32Mem : IdealMemCertificate O ℤ B I3
  ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] ![-31, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 30
 C := ![-31, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log32Mem
 k :=  15
 hpow := by decide
 heql := by decide

def Log33Mem : IdealMemCertificate O ℤ B I3
  ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] ![33909, 20880, 13147, 17954, -47580] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![11980, 20880, 13147, 17954, -47580]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![33937, 20880, 13147, 17954, -47580]
 hxeq :=  rfl
 m:= 28
 C := ![33909, 20880, 13147, 17954, -47580]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log33Mem
 k :=  16
 hpow := by decide
 heql := by decide

def Log34Mem : IdealMemCertificate O ℤ B I3
  ![![31, 0, 0, 0, 0], ![20, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![22, 0, 0, 1, 0], ![25, 0, 0, 0, 1]] ![186, 109, 64, 85, -223] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A3
 g := ![49, 109, 64, 85, -223]
 hmem := by decide

def Log34: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R31) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![194, 109, 64, 85, -223]
 hxeq :=  rfl
 m:= 8
 C := ![186, 109, 64, 85, -223]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log34Mem
 k :=  12
 hpow := by decide
 heql := by decide

def Log40Mem : IdealMemCertificate O ℤ B I4
  ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![72620, -21683, 6662, 13571, -23580] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A4
 g := ![32095, -21683, 6662, 13571, -23580]
 hmem := by decide

def Log40: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![72622, -21683, 6662, 13571, -23580]
 hxeq :=  rfl
 m:= 2
 C := ![72620, -21683, 6662, 13571, -23580]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log40Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log41Mem : IdealMemCertificate O ℤ B I4
  ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-924607, -3154467, -3847477, -4269764, 10021778] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A4
 g := ![-948525, -3154467, -3847477, -4269764, 10021778]
 hmem := by decide

def Log41: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-924605, -3154467, -3847477, -4269764, 10021778]
 hxeq :=  rfl
 m:= 2
 C := ![-924607, -3154467, -3847477, -4269764, 10021778]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log41Mem
 k :=  2
 hpow := by decide
 heql := by decide

def Log42Mem : IdealMemCertificate O ℤ B I4
  ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![-7, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A4
 g := ![-1, 0, 0, 0, 0]
 hmem := by decide

def Log42: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![-1, 0, 0, 0, 0]
 hxeq :=  rfl
 m:= 6
 C := ![-7, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log42Mem
 k :=  3
 hpow := by decide
 heql := by decide

def Log43Mem : IdealMemCertificate O ℤ B I4
  ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![33932, 20880, 13147, 17954, -47580] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A4
 g := ![8025, 20880, 13147, 17954, -47580]
 hmem := by decide

def Log43: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![33937, 20880, 13147, 17954, -47580]
 hxeq :=  rfl
 m:= 5
 C := ![33932, 20880, 13147, 17954, -47580]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log43Mem
 k :=  5
 hpow := by decide
 heql := by decide

def Log44Mem : IdealMemCertificate O ℤ B I4
  ![![7, 0, 0, 0, 0], ![5, 1, 0, 0, 0], ![3, 0, 1, 0, 0], ![4, 0, 0, 1, 0], ![5, 0, 0, 0, 1]] ![193, 109, 64, 85, -223] where
 hieq := ideal_eq_of_IdealEqSpanCertificate _ _ A4
 g := ![33, 109, 64, 85, -223]
 hmem := by decide

def Log44: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R7) ▸ IsPrimitiveRoot.orderOf _) 2 alpha1 0 where
 r := 5
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord :=  ![194, 109, 64, 85, -223]
 hxeq :=  rfl
 m:= 1
 C := ![193, 109, 64, 85, -223]
 hCeq := by rfl
 hmem := mem_of_certificate O ℤ _ _ _ _ Log44Mem
 k :=  0
 hpow := by decide
 heql := by decide

end Sat2
