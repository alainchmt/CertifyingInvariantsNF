import IdealArithmetic.Examples.NF8_0_64000000_3.ClassGroupData8_0_64000000_3
import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Saturation.PrincipalityCertificate
import IdealArithmetic.Computation.ExponentiationZMod
import Mathlib.RingTheory.AdjoinRoot
import IdealArithmetic.Examples.NF8_0_64000000_3.RI8_0_64000000_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial

noncomputable section

namespace Sat2 
instance hq101 : Fact $ Nat.Prime 101 := {out := by norm_num}
instance hq5 : Fact $ Nat.Prime 5 := {out := by norm_num}

def R101 : IsOrderOf (2 : ZMod 101) 100 where
 m := 2
 P := ![2, 5]
 e := ![2, 2]
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

def I0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0, 0, 0]] i)))
def I1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0]] i)))
def I2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0, 0, 0, 0], ![6, 1, 0, 0, 0, 0, 0, 0]] i)))
def I3 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0, 0, 0, 0], ![40, 1, 0, 0, 0, 0, 0, 0]] i)))
def I4 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![101, 0, 0, 0, 0, 0, 0, 0], ![30, 1, 0, 0, 0, 0, 0, 0]] i)))

def A0: IdealEqSpanCertificate' Table ![![5, 0, 0, 0, 0, 0, 0, 0], ![-2, 1, 0, 0, 0, 0, 0, 0]] 
 ![![5, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 0, 0], ![4, 0, 0, 0, 1, 0, 0, 0], ![3, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![2, 0, 0, 0, 0, 0, 0, 1]] where
  M :=![![![5, 0, 0, 0, 0, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0], ![0, 0, 5, 0, 0, 0, 0, 0], ![0, 0, 0, 5, 0, 0, 0, 0], ![0, 0, 0, 0, 5, 0, 0, 0], ![0, 0, 0, 0, 0, 5, 0, 0], ![0, 0, 0, 0, 0, 0, 5, 0], ![0, 0, 0, 0, 0, 0, 0, 5]], ![![-2, 1, 0, 0, 0, 0, 0, 0], ![0, -2, 1, 0, 0, 0, 0, 0], ![0, 0, -2, 1, 0, 0, 0, 0], ![0, 0, 0, -2, 1, 0, 0, 0], ![0, 0, 0, 0, -2, 1, 0, 0], ![0, 0, 0, 0, 0, -2, 1, 0], ![2, 8, -1, -1, -1, -1, -9, 21], ![1, 4, -1, 0, -1, 0, -4, 9]]]
  hmulB := by decide  
  f := ![![![59, 49, -22, 167, 295, 190, -210, 42], ![135, 150, 25, 435, 960, 960, -10, 0]], ![![55, 57, -25, 161, 292, 193, -210, 42], ![126, 165, 25, 420, 945, 960, -10, 0]], ![![51, 63, -29, 156, 283, 193, -207, 42], ![117, 176, 20, 405, 915, 945, -10, 0]], ![![50, 62, -28, 156, 289, 190, -207, 42], ![114, 172, 21, 405, 930, 945, -10, 0]], ![![60, 50, -22, 163, 291, 193, -210, 42], ![138, 154, 27, 426, 945, 960, -10, 0]], ![![55, 58, -26, 160, 289, 189, -207, 42], ![126, 168, 24, 417, 936, 945, -10, 0]], ![![1, 2, 0, 3, 3, 0, -1, 0], ![2, 6, 3, 9, 12, 6, 0, 0]], ![![26, 20, -8, 66, 118, 76, -84, 17], ![60, 64, 14, 174, 384, 384, -4, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![-3, 5, 0, 0, 0, 0, 0, 0], ![-1, 0, 5, 0, 0, 0, 0, 0], ![-2, 0, 0, 5, 0, 0, 0, 0], ![-4, 0, 0, 0, 5, 0, 0, 0], ![-3, 0, 0, 0, 0, 5, 0, 0], ![-1, 0, 0, 0, 0, 0, 5, 0], ![-2, 0, 0, 0, 0, 0, 0, 5]], ![![-1, 1, 0, 0, 0, 0, 0, 0], ![1, -2, 1, 0, 0, 0, 0, 0], ![0, 0, -2, 1, 0, 0, 0, 0], ![0, 0, 0, -2, 1, 0, 0, 0], ![1, 0, 0, 0, -2, 1, 0, 0], ![1, 0, 0, 0, 0, -2, 1, 0], ![-9, 8, -1, -1, -1, -1, -9, 21], ![-4, 4, -1, 0, -1, 0, -4, 9]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N0 : Nat.card (O ⧸ I0) = 5 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0)

def A1: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![92, 0, 1, 0, 0, 0, 0, 0], ![27, 0, 0, 1, 0, 0, 0, 0], ![20, 0, 0, 0, 1, 0, 0, 0], ![41, 0, 0, 0, 0, 1, 0, 0], ![79, 0, 0, 0, 0, 0, 1, 0], ![37, 0, 0, 0, 0, 0, 0, 1]] where
  M :=![![![101, 0, 0, 0, 0, 0, 0, 0], ![0, 101, 0, 0, 0, 0, 0, 0], ![0, 0, 101, 0, 0, 0, 0, 0], ![0, 0, 0, 101, 0, 0, 0, 0], ![0, 0, 0, 0, 101, 0, 0, 0], ![0, 0, 0, 0, 0, 101, 0, 0], ![0, 0, 0, 0, 0, 0, 101, 0], ![0, 0, 0, 0, 0, 0, 0, 101]], ![![3, 1, 0, 0, 0, 0, 0, 0], ![0, 3, 1, 0, 0, 0, 0, 0], ![0, 0, 3, 1, 0, 0, 0, 0], ![0, 0, 0, 3, 1, 0, 0, 0], ![0, 0, 0, 0, 3, 1, 0, 0], ![0, 0, 0, 0, 0, 3, 1, 0], ![2, 8, -1, -1, -1, -1, -4, 21], ![1, 4, -1, 0, -1, 0, -4, 14]]]
  hmulB := by decide  
  f := ![![![3975991, -79055785, -284317325, -85959615, 148995239, 585660822, 178636074, 137592], ![-133417162, 2707781821, 8669202084, 4019093, -5017733328, -18044890482, -661752, 0]], ![![152913, -3040550, -10935251, -3306137, 5730515, 22525428, 6870630, 5292], ![-5131102, 104143423, 333430492, 154631, -192987366, -694035438, -25452, 0]], ![![3670144, -72974482, -262446663, -79347314, 137534004, 540609898, 164894814, 127008], ![-123154252, 2499487906, 8002338070, 3709932, -4631751728, -16656819606, -610848, 0]], ![![1070457, -21284236, -76546962, -23142973, 40114118, 157677962, 48094342, 37044], ![-35919934, 729017694, 2334015768, 1082114, -1350928732, -4858241198, -178164, 0]], ![![815584, -16216531, -58321451, -17632730, 30563055, 120135514, 36643292, 28224], ![-27367492, 555441025, 1778296594, 824464, -1029276254, -3701515468, -135744, 0]], ![![1631167, -32433118, -116642972, -35265477, 61126209, 240271061, 73286584, 56448], ![-54734950, 1110883924, 3556594920, 1648923, -2058555840, -7403030936, -271488, 0]], ![![3109433, -61825674, -222350728, -67224827, 116521919, 458016798, 139702571, 107604], ![-104339202, 2117624156, 6779760616, 3143129, -3924124824, -14112029766, -517524, 0]], ![![1456547, -28961031, -104155855, -31490158, 54582414, 214549014, 65440938, 50405], ![-48875454, 991959659, 3175846424, 1472370, -1838179536, -6610504434, -242424, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![-3, 101, 0, 0, 0, 0, 0, 0], ![-92, 0, 101, 0, 0, 0, 0, 0], ![-27, 0, 0, 101, 0, 0, 0, 0], ![-20, 0, 0, 0, 101, 0, 0, 0], ![-41, 0, 0, 0, 0, 101, 0, 0], ![-79, 0, 0, 0, 0, 0, 101, 0], ![-37, 0, 0, 0, 0, 0, 0, 101]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![-1, 3, 1, 0, 0, 0, 0, 0], ![-3, 0, 3, 1, 0, 0, 0, 0], ![-1, 0, 0, 3, 1, 0, 0, 0], ![-1, 0, 0, 0, 3, 1, 0, 0], ![-2, 0, 0, 0, 0, 3, 1, 0], ![-3, 8, -1, -1, -1, -1, -4, 21], ![-1, 4, -1, 0, -1, 0, -4, 14]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N1 : Nat.card (O ⧸ I1) = 101 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1)

def A2: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0, 0, 0, 0], ![6, 1, 0, 0, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![6, 1, 0, 0, 0, 0, 0, 0], ![65, 0, 1, 0, 0, 0, 0, 0], ![14, 0, 0, 1, 0, 0, 0, 0], ![17, 0, 0, 0, 1, 0, 0, 0], ![100, 0, 0, 0, 0, 1, 0, 0], ![6, 0, 0, 0, 0, 0, 1, 0], ![94, 0, 0, 0, 0, 0, 0, 1]] where
  M :=![![![101, 0, 0, 0, 0, 0, 0, 0], ![0, 101, 0, 0, 0, 0, 0, 0], ![0, 0, 101, 0, 0, 0, 0, 0], ![0, 0, 0, 101, 0, 0, 0, 0], ![0, 0, 0, 0, 101, 0, 0, 0], ![0, 0, 0, 0, 0, 101, 0, 0], ![0, 0, 0, 0, 0, 0, 101, 0], ![0, 0, 0, 0, 0, 0, 0, 101]], ![![6, 1, 0, 0, 0, 0, 0, 0], ![0, 6, 1, 0, 0, 0, 0, 0], ![0, 0, 6, 1, 0, 0, 0, 0], ![0, 0, 0, 6, 1, 0, 0, 0], ![0, 0, 0, 0, 6, 1, 0, 0], ![0, 0, 0, 0, 0, 6, 1, 0], ![2, 8, -1, -1, -1, -1, -1, 21], ![1, 4, -1, 0, -1, 0, -4, 17]]]
  hmulB := by decide  
  f := ![![![909415, -8815535, -39317155, -32264915, -4353291, 17514772, 2918900, 23562], ![-15270695, 151091051, 636638047, 437000841, 428038, -294922222, -113322, 0]], ![![106950, -1036821, -4625375, -3795490, -512094, 2059973, 343302, 2772], ![-1795880, 17770243, 74896550, 51405768, 50399, -34686834, -13332, 0]], ![![588433, -5704158, -25440502, -20877297, -2816834, 11333118, 1888705, 15246], ![-9880836, 97764567, 411942135, 282765256, 276942, -190832531, -73326, 0]], ![![160450, -1555500, -6938198, -5693544, -768187, 3090470, 515038, 4158], ![-2694240, 26659954, 112346341, 77113601, 75548, -52038836, -19998, 0]], ![![160477, -1555660, -6938309, -5693756, -768220, 3090776, 515089, 4158], ![-2694694, 26662723, 112347748, 77116935, 75548, -52043987, -19998, 0]], ![![909386, -8815485, -39317124, -32264845, -4353280, 17514670, 2918883, 23562], ![-15270207, 151090128, 636637679, 436999724, 428039, -294920505, -113322, 0]], ![![53472, -518575, -2312780, -1897950, -256082, 1030286, 171701, 1386], ![-897889, 8887882, 37449372, 25706152, 25244, -17348466, -6666, 0]], ![![846380, -8204551, -36592206, -30028738, -4051578, 16300877, 2716600, 21929], ![-14212225, 140619270, 592514678, 406713732, 398363, -274482068, -105468, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![-6, 101, 0, 0, 0, 0, 0, 0], ![-65, 0, 101, 0, 0, 0, 0, 0], ![-14, 0, 0, 101, 0, 0, 0, 0], ![-17, 0, 0, 0, 101, 0, 0, 0], ![-100, 0, 0, 0, 0, 101, 0, 0], ![-6, 0, 0, 0, 0, 0, 101, 0], ![-94, 0, 0, 0, 0, 0, 0, 101]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![-1, 6, 1, 0, 0, 0, 0, 0], ![-4, 0, 6, 1, 0, 0, 0, 0], ![-1, 0, 0, 6, 1, 0, 0, 0], ![-2, 0, 0, 0, 6, 1, 0, 0], ![-6, 0, 0, 0, 0, 6, 1, 0], ![-18, 8, -1, -1, -1, -1, -1, 21], ![-15, 4, -1, 0, -1, 0, -4, 17]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N2 : Nat.card (O ⧸ I2) = 101 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2)

def A3: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0, 0, 0, 0], ![40, 1, 0, 0, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![40, 1, 0, 0, 0, 0, 0, 0], ![16, 0, 1, 0, 0, 0, 0, 0], ![67, 0, 0, 1, 0, 0, 0, 0], ![47, 0, 0, 0, 1, 0, 0, 0], ![39, 0, 0, 0, 0, 1, 0, 0], ![56, 0, 0, 0, 0, 0, 1, 0], ![54, 0, 0, 0, 0, 0, 0, 1]] where
  M :=![![![101, 0, 0, 0, 0, 0, 0, 0], ![0, 101, 0, 0, 0, 0, 0, 0], ![0, 0, 101, 0, 0, 0, 0, 0], ![0, 0, 0, 101, 0, 0, 0, 0], ![0, 0, 0, 0, 101, 0, 0, 0], ![0, 0, 0, 0, 0, 101, 0, 0], ![0, 0, 0, 0, 0, 0, 101, 0], ![0, 0, 0, 0, 0, 0, 0, 101]], ![![40, 1, 0, 0, 0, 0, 0, 0], ![0, 40, 1, 0, 0, 0, 0, 0], ![0, 0, 40, 1, 0, 0, 0, 0], ![0, 0, 0, 40, 1, 0, 0, 0], ![0, 0, 0, 0, 40, 1, 0, 0], ![0, 0, 0, 0, 0, 40, 1, 0], ![2, 8, -1, -1, -1, -1, 33, 21], ![1, 4, -1, 0, -1, 0, -4, 51]]]
  hmulB := by decide  
  f := ![![![44440345, -1298859268, -51371870, 4306368956, 11611249668, 4494196596, 105411276, 156492], ![-112174236, 3282574538, 47630792, -10874791200, -29046554448, -10621701360, -752652, 0]], ![![17872634, -522366798, -20660413, 1731908461, 4669743051, 1807448811, 42393669, 62937], ![-45113265, 1320164536, 19155862, -4373555328, -11681769888, -4271771568, -302697, 0]], ![![7245686, -211770119, -8375838, 702125415, 1893138513, 732750801, 17186655, 25515], ![-18289221, 535201324, 7765890, -1773063888, -4735851216, -1731802560, -122715, 0]], ![![29948891, -875317257, -34620150, 2902116206, 7824972594, 3028696914, 71038014, 105462], ![-75595587, 2212167408, 32099013, -7328658576, -19574852016, -7158101088, -507222, 0]], ![![20770993, -607075349, -24010785, 2012759018, 5426996930, 2100549093, 49268331, 73143], ![-52429167, 1534246342, 22262279, -5082781872, -13576106496, -4964492592, -351783, 0]], ![![17389611, -508248811, -20102018, 1685099924, 4543532028, 1758598073, 41247876, 61236], ![-43894041, 1284484502, 18638120, -4255350624, -11366041968, -4156316448, -294516, 0]], ![![24635398, -720019855, -28477899, 2387226289, 6436671021, 2491348125, 58434512, 86751], ![-62183517, 1819688168, 26404060, -6028416912, -16101894336, -5888117088, -417231, 0]], ![![23760150, -694439619, -27466164, 2302415085, 6207994872, 2402837784, 56358504, 83669], ![-59974257, 1755039876, 25466007, -5814244800, -15529840992, -5678929440, -402408, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![-40, 101, 0, 0, 0, 0, 0, 0], ![-16, 0, 101, 0, 0, 0, 0, 0], ![-67, 0, 0, 101, 0, 0, 0, 0], ![-47, 0, 0, 0, 101, 0, 0, 0], ![-39, 0, 0, 0, 0, 101, 0, 0], ![-56, 0, 0, 0, 0, 0, 101, 0], ![-54, 0, 0, 0, 0, 0, 0, 101]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![-16, 40, 1, 0, 0, 0, 0, 0], ![-7, 0, 40, 1, 0, 0, 0, 0], ![-27, 0, 0, 40, 1, 0, 0, 0], ![-19, 0, 0, 0, 40, 1, 0, 0], ![-16, 0, 0, 0, 0, 40, 1, 0], ![-31, 8, -1, -1, -1, -1, 33, 21], ![-26, 4, -1, 0, -1, 0, -4, 51]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N3 : Nat.card (O ⧸ I3) = 101 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3)

def A4: IdealEqSpanCertificate' Table ![![101, 0, 0, 0, 0, 0, 0, 0], ![30, 1, 0, 0, 0, 0, 0, 0]] 
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![30, 1, 0, 0, 0, 0, 0, 0], ![9, 0, 1, 0, 0, 0, 0, 0], ![33, 0, 0, 1, 0, 0, 0, 0], ![20, 0, 0, 0, 1, 0, 0, 0], ![6, 0, 0, 0, 0, 1, 0, 0], ![22, 0, 0, 0, 0, 0, 1, 0], ![64, 0, 0, 0, 0, 0, 0, 1]] where
  M :=![![![101, 0, 0, 0, 0, 0, 0, 0], ![0, 101, 0, 0, 0, 0, 0, 0], ![0, 0, 101, 0, 0, 0, 0, 0], ![0, 0, 0, 101, 0, 0, 0, 0], ![0, 0, 0, 0, 101, 0, 0, 0], ![0, 0, 0, 0, 0, 101, 0, 0], ![0, 0, 0, 0, 0, 0, 101, 0], ![0, 0, 0, 0, 0, 0, 0, 101]], ![![30, 1, 0, 0, 0, 0, 0, 0], ![0, 30, 1, 0, 0, 0, 0, 0], ![0, 0, 30, 1, 0, 0, 0, 0], ![0, 0, 0, 30, 1, 0, 0, 0], ![0, 0, 0, 0, 30, 1, 0, 0], ![0, 0, 0, 0, 0, 30, 1, 0], ![2, 8, -1, -1, -1, -1, 23, 21], ![1, 4, -1, 0, -1, 0, -4, 41]]]
  hmulB := by decide  
  f := ![![![11234845, -456917338, -20408144, 1465148860, 1814719924, 2451482100, 79798484, 40572], ![-37810966, 1539600772, 17380888, -4933253696, -5945121792, -8055158848, -195132, 0]], ![![3419256, -139060900, -6211156, 445915037, 552305652, 746104820, 24286548, 12348], ![-11507535, 468571118, 5289875, -1501425600, -1809383488, -2451575424, -59388, 0]], ![![1465263, -59592849, -2661755, 191103702, 236695748, 319757892, 10408484, 5292], ![-4931355, 200800424, 2267046, -643458880, -775427904, -1050671488, -25452, 0]], ![![3907707, -158925183, -7098408, 509614991, 631204192, 852689504, 27756000, 14112], ![-13151421, 535504596, 6045558, -1715907584, -2067859456, -2801794944, -67872, 0]], ![![2442250, -99327487, -4436482, 318508799, 394500681, 532931356, 17347516, 8820], ![-8219413, 334687832, 3778481, -1072440320, -1292405696, -1751123456, -42420, 0]], ![![976812, -39728547, -1774500, 127401657, 157796568, 213171269, 6938968, 3528], ![-3287469, 133866882, 1511355, -428969856, -516950016, -700445504, -16968, 0]], ![![2442302, -99329912, -4436562, 318510662, 394504412, 532930908, 17347497, 8820], ![-8219588, 334696002, 3778478, -1072446592, -1292418048, -1751121536, -42420, 0]], ![![7119050, -289531793, -12931918, 928411158, 1149921536, 1553414400, 50565376, 25709], ![-23959223, 975588650, 11013714, -3126022144, -3767205888, -5104259072, -123648, 0]]]
  g := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![-30, 101, 0, 0, 0, 0, 0, 0], ![-9, 0, 101, 0, 0, 0, 0, 0], ![-33, 0, 0, 101, 0, 0, 0, 0], ![-20, 0, 0, 0, 101, 0, 0, 0], ![-6, 0, 0, 0, 0, 101, 0, 0], ![-22, 0, 0, 0, 0, 0, 101, 0], ![-64, 0, 0, 0, 0, 0, 0, 101]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![-9, 30, 1, 0, 0, 0, 0, 0], ![-3, 0, 30, 1, 0, 0, 0, 0], ![-10, 0, 0, 30, 1, 0, 0, 0], ![-6, 0, 0, 0, 30, 1, 0, 0], ![-2, 0, 0, 0, 0, 30, 1, 0], ![-20, 8, -1, -1, -1, -1, 23, 21], ![-26, 4, -1, 0, -1, 0, -4, 41]]]
  hle1 := by decide   
  hle2 := by decide  

lemma N4 : Nat.card (O ⧸ I4) = 101 := 
ideal_norm_eq_prod' B _ _ (by decide) 0 0 (by decide) (ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4)

def Log00Mem : IdealMemCertificate B I0
 ![![5, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 0, 0], ![4, 0, 0, 0, 1, 0, 0, 0], ![3, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![2, 0, 0, 0, 0, 0, 0, 1]] ![-1, 2, -2, 2, -3, 2, -4, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-3, 2, -2, 2, -3, 2, -4, 8]
 hmem := by decide

def Log00: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, 2, -2, 2, -3, 2, -4, 8]
 hxeq :=  rfl
 m := 2
 C := ![-1, 2, -2, 2, -3, 2, -4, 8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log00Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log01Mem : IdealMemCertificate B I0
 ![![5, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 0, 0], ![4, 0, 0, 0, 1, 0, 0, 0], ![3, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![2, 0, 0, 0, 0, 0, 0, 1]] ![-2, 1, 0, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-1, 1, 0, 0, 0, 0, 0, 0]
 hmem := by decide

def Log01: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![0, 1, 0, 0, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 2
 C := ![-2, 1, 0, 0, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log01Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log02Mem : IdealMemCertificate B I0
 ![![5, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 0, 0], ![4, 0, 0, 0, 1, 0, 0, 0], ![3, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![2, 0, 0, 0, 0, 0, 0, 1]] ![-1, -1, 0, 0, 0, 0, 2, -5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![2, -1, 0, 0, 0, 0, 2, -5]
 hmem := by decide

def Log02: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, -1, 0, 0, 0, 0, 2, -5]
 hxeq :=  rfl
 m := 2
 C := ![-1, -1, 0, 0, 0, 0, 2, -5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log02Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log03Mem : IdealMemCertificate B I0
 ![![5, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 0, 0], ![4, 0, 0, 0, 1, 0, 0, 0], ![3, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![2, 0, 0, 0, 0, 0, 0, 1]] ![-4, -5, 5, -5, 5, -3, 5, -10] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![4, -5, 5, -5, 5, -3, 5, -10]
 hmem := by decide

def Log03: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, -5, 5, -5, 5, -3, 5, -10]
 hxeq :=  rfl
 m := 3
 C := ![-4, -5, 5, -5, 5, -3, 5, -10]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log03Mem
 k := 3
 hpow := by zmod_pow
 heql := by decide

def Log04Mem : IdealMemCertificate B I0
 ![![5, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![1, 0, 1, 0, 0, 0, 0, 0], ![2, 0, 0, 1, 0, 0, 0, 0], ![4, 0, 0, 0, 1, 0, 0, 0], ![3, 0, 0, 0, 0, 1, 0, 0], ![1, 0, 0, 0, 0, 0, 1, 0], ![2, 0, 0, 0, 0, 0, 0, 1]] ![0, 5, -6, 5, -5, 3, -3, 5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A0
 g := ![-3, 5, -6, 5, -5, 3, -3, 5]
 hmem := by decide

def Log04: DiscreteLogCertificate N0 ((orderOf_of_IsOrderOf R5) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2, 5, -6, 5, -5, 3, -3, 5]
 hxeq :=  rfl
 m := 2
 C := ![0, 5, -6, 5, -5, 3, -3, 5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log04Mem
 k := 1
 hpow := by zmod_pow
 heql := by decide

def Log10Mem : IdealMemCertificate B I1
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![92, 0, 1, 0, 0, 0, 0, 0], ![27, 0, 0, 1, 0, 0, 0, 0], ![20, 0, 0, 0, 1, 0, 0, 0], ![41, 0, 0, 0, 0, 1, 0, 0], ![79, 0, 0, 0, 0, 0, 1, 0], ![37, 0, 0, 0, 0, 0, 0, 1]] ![-21, 2, -2, 2, -3, 2, -4, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![1, 2, -2, 2, -3, 2, -4, 8]
 hmem := by decide

def Log10: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, 2, -2, 2, -3, 2, -4, 8]
 hxeq :=  rfl
 m := 22
 C := ![-21, 2, -2, 2, -3, 2, -4, 8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log10Mem
 k := 14
 hpow := by zmod_pow
 heql := by decide

def Log11Mem : IdealMemCertificate B I1
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![92, 0, 1, 0, 0, 0, 0, 0], ![27, 0, 0, 1, 0, 0, 0, 0], ![20, 0, 0, 0, 1, 0, 0, 0], ![41, 0, 0, 0, 0, 1, 0, 0], ![79, 0, 0, 0, 0, 0, 1, 0], ![37, 0, 0, 0, 0, 0, 0, 1]] ![-98, 1, 0, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-1, 1, 0, 0, 0, 0, 0, 0]
 hmem := by decide

def Log11: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![0, 1, 0, 0, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 98
 C := ![-98, 1, 0, 0, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log11Mem
 k := 19
 hpow := by zmod_pow
 heql := by decide

def Log12Mem : IdealMemCertificate B I1
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![92, 0, 1, 0, 0, 0, 0, 0], ![27, 0, 0, 1, 0, 0, 0, 0], ![20, 0, 0, 0, 1, 0, 0, 0], ![41, 0, 0, 0, 0, 1, 0, 0], ![79, 0, 0, 0, 0, 0, 1, 0], ![37, 0, 0, 0, 0, 0, 0, 1]] ![-30, -1, 0, 0, 0, 0, 2, -5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![0, -1, 0, 0, 0, 0, 2, -5]
 hmem := by decide

def Log12: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, -1, 0, 0, 0, 0, 2, -5]
 hxeq :=  rfl
 m := 31
 C := ![-30, -1, 0, 0, 0, 0, 2, -5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log12Mem
 k := 84
 hpow := by zmod_pow
 heql := by decide

def Log13Mem : IdealMemCertificate B I1
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![92, 0, 1, 0, 0, 0, 0, 0], ![27, 0, 0, 1, 0, 0, 0, 0], ![20, 0, 0, 0, 1, 0, 0, 0], ![41, 0, 0, 0, 0, 1, 0, 0], ![79, 0, 0, 0, 0, 0, 1, 0], ![37, 0, 0, 0, 0, 0, 0, 1]] ![-92, -5, 5, -5, 5, -3, 5, -10] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![-4, -5, 5, -5, 5, -3, 5, -10]
 hmem := by decide

def Log13: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, -5, 5, -5, 5, -3, 5, -10]
 hxeq :=  rfl
 m := 91
 C := ![-92, -5, 5, -5, 5, -3, 5, -10]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log13Mem
 k := 75
 hpow := by zmod_pow
 heql := by decide

def Log14Mem : IdealMemCertificate B I1
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![3, 1, 0, 0, 0, 0, 0, 0], ![92, 0, 1, 0, 0, 0, 0, 0], ![27, 0, 0, 1, 0, 0, 0, 0], ![20, 0, 0, 0, 1, 0, 0, 0], ![41, 0, 0, 0, 0, 1, 0, 0], ![79, 0, 0, 0, 0, 0, 1, 0], ![37, 0, 0, 0, 0, 0, 0, 1]] ![-27, 5, -6, 5, -5, 3, -3, 5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A1
 g := ![4, 5, -6, 5, -5, 3, -3, 5]
 hmem := by decide

def Log14: DiscreteLogCertificate N1 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2, 5, -6, 5, -5, 3, -3, 5]
 hxeq :=  rfl
 m := 29
 C := ![-27, 5, -6, 5, -5, 3, -3, 5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log14Mem
 k := 91
 hpow := by zmod_pow
 heql := by decide

def Log20Mem : IdealMemCertificate B I2
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![6, 1, 0, 0, 0, 0, 0, 0], ![65, 0, 1, 0, 0, 0, 0, 0], ![14, 0, 0, 1, 0, 0, 0, 0], ![17, 0, 0, 0, 1, 0, 0, 0], ![100, 0, 0, 0, 0, 1, 0, 0], ![6, 0, 0, 0, 0, 0, 1, 0], ![94, 0, 0, 0, 0, 0, 0, 1]] ![-21, 2, -2, 2, -3, 2, -4, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-8, 2, -2, 2, -3, 2, -4, 8]
 hmem := by decide

def Log20: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, 2, -2, 2, -3, 2, -4, 8]
 hxeq :=  rfl
 m := 22
 C := ![-21, 2, -2, 2, -3, 2, -4, 8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log20Mem
 k := 14
 hpow := by zmod_pow
 heql := by decide

def Log21Mem : IdealMemCertificate B I2
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![6, 1, 0, 0, 0, 0, 0, 0], ![65, 0, 1, 0, 0, 0, 0, 0], ![14, 0, 0, 1, 0, 0, 0, 0], ![17, 0, 0, 0, 1, 0, 0, 0], ![100, 0, 0, 0, 0, 1, 0, 0], ![6, 0, 0, 0, 0, 0, 1, 0], ![94, 0, 0, 0, 0, 0, 0, 1]] ![-95, 1, 0, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-1, 1, 0, 0, 0, 0, 0, 0]
 hmem := by decide

def Log21: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![0, 1, 0, 0, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 95
 C := ![-95, 1, 0, 0, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log21Mem
 k := 20
 hpow := by zmod_pow
 heql := by decide

def Log22Mem : IdealMemCertificate B I2
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![6, 1, 0, 0, 0, 0, 0, 0], ![65, 0, 1, 0, 0, 0, 0, 0], ![14, 0, 0, 1, 0, 0, 0, 0], ![17, 0, 0, 0, 1, 0, 0, 0], ![100, 0, 0, 0, 0, 1, 0, 0], ![6, 0, 0, 0, 0, 0, 1, 0], ![94, 0, 0, 0, 0, 0, 0, 1]] ![-60, -1, 0, 0, 0, 0, 2, -5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![4, -1, 0, 0, 0, 0, 2, -5]
 hmem := by decide

def Log22: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, -1, 0, 0, 0, 0, 2, -5]
 hxeq :=  rfl
 m := 61
 C := ![-60, -1, 0, 0, 0, 0, 2, -5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log22Mem
 k := 77
 hpow := by zmod_pow
 heql := by decide

def Log23Mem : IdealMemCertificate B I2
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![6, 1, 0, 0, 0, 0, 0, 0], ![65, 0, 1, 0, 0, 0, 0, 0], ![14, 0, 0, 1, 0, 0, 0, 0], ![17, 0, 0, 0, 1, 0, 0, 0], ![100, 0, 0, 0, 0, 1, 0, 0], ![6, 0, 0, 0, 0, 0, 1, 0], ![94, 0, 0, 0, 0, 0, 0, 1]] ![-92, -5, 5, -5, 5, -3, 5, -10] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![8, -5, 5, -5, 5, -3, 5, -10]
 hmem := by decide

def Log23: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, -5, 5, -5, 5, -3, 5, -10]
 hxeq :=  rfl
 m := 91
 C := ![-92, -5, 5, -5, 5, -3, 5, -10]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log23Mem
 k := 75
 hpow := by zmod_pow
 heql := by decide

def Log24Mem : IdealMemCertificate B I2
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![6, 1, 0, 0, 0, 0, 0, 0], ![65, 0, 1, 0, 0, 0, 0, 0], ![14, 0, 0, 1, 0, 0, 0, 0], ![17, 0, 0, 0, 1, 0, 0, 0], ![100, 0, 0, 0, 0, 1, 0, 0], ![6, 0, 0, 0, 0, 0, 1, 0], ![94, 0, 0, 0, 0, 0, 0, 1]] ![-27, 5, -6, 5, -5, 3, -3, 5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A2
 g := ![-4, 5, -6, 5, -5, 3, -3, 5]
 hmem := by decide

def Log24: DiscreteLogCertificate N2 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2, 5, -6, 5, -5, 3, -3, 5]
 hxeq :=  rfl
 m := 29
 C := ![-27, 5, -6, 5, -5, 3, -3, 5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log24Mem
 k := 91
 hpow := by zmod_pow
 heql := by decide

def Log30Mem : IdealMemCertificate B I3
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![40, 1, 0, 0, 0, 0, 0, 0], ![16, 0, 1, 0, 0, 0, 0, 0], ![67, 0, 0, 1, 0, 0, 0, 0], ![47, 0, 0, 0, 1, 0, 0, 0], ![39, 0, 0, 0, 0, 1, 0, 0], ![56, 0, 0, 0, 0, 0, 1, 0], ![54, 0, 0, 0, 0, 0, 0, 1]] ![-77, 2, -2, 2, -3, 2, -4, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-4, 2, -2, 2, -3, 2, -4, 8]
 hmem := by decide

def Log30: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, 2, -2, 2, -3, 2, -4, 8]
 hxeq :=  rfl
 m := 78
 C := ![-77, 2, -2, 2, -3, 2, -4, 8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log30Mem
 k := 36
 hpow := by zmod_pow
 heql := by decide

def Log31Mem : IdealMemCertificate B I3
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![40, 1, 0, 0, 0, 0, 0, 0], ![16, 0, 1, 0, 0, 0, 0, 0], ![67, 0, 0, 1, 0, 0, 0, 0], ![47, 0, 0, 0, 1, 0, 0, 0], ![39, 0, 0, 0, 0, 1, 0, 0], ![56, 0, 0, 0, 0, 0, 1, 0], ![54, 0, 0, 0, 0, 0, 0, 1]] ![-61, 1, 0, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-1, 1, 0, 0, 0, 0, 0, 0]
 hmem := by decide

def Log31: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![0, 1, 0, 0, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 61
 C := ![-61, 1, 0, 0, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log31Mem
 k := 77
 hpow := by zmod_pow
 heql := by decide

def Log32Mem : IdealMemCertificate B I3
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![40, 1, 0, 0, 0, 0, 0, 0], ![16, 0, 1, 0, 0, 0, 0, 0], ![67, 0, 0, 1, 0, 0, 0, 0], ![47, 0, 0, 0, 1, 0, 0, 0], ![39, 0, 0, 0, 0, 1, 0, 0], ![56, 0, 0, 0, 0, 0, 1, 0], ![54, 0, 0, 0, 0, 0, 0, 1]] ![-97, -1, 0, 0, 0, 0, 2, -5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![1, -1, 0, 0, 0, 0, 2, -5]
 hmem := by decide

def Log32: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, -1, 0, 0, 0, 0, 2, -5]
 hxeq :=  rfl
 m := 98
 C := ![-97, -1, 0, 0, 0, 0, 2, -5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log32Mem
 k := 19
 hpow := by zmod_pow
 heql := by decide

def Log33Mem : IdealMemCertificate B I3
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![40, 1, 0, 0, 0, 0, 0, 0], ![16, 0, 1, 0, 0, 0, 0, 0], ![67, 0, 0, 1, 0, 0, 0, 0], ![47, 0, 0, 0, 1, 0, 0, 0], ![39, 0, 0, 0, 0, 1, 0, 0], ![56, 0, 0, 0, 0, 0, 1, 0], ![54, 0, 0, 0, 0, 0, 0, 1]] ![-92, -5, 5, -5, 5, -3, 5, -10] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![5, -5, 5, -5, 5, -3, 5, -10]
 hmem := by decide

def Log33: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, -5, 5, -5, 5, -3, 5, -10]
 hxeq :=  rfl
 m := 91
 C := ![-92, -5, 5, -5, 5, -3, 5, -10]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log33Mem
 k := 75
 hpow := by zmod_pow
 heql := by decide

def Log34Mem : IdealMemCertificate B I3
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![40, 1, 0, 0, 0, 0, 0, 0], ![16, 0, 1, 0, 0, 0, 0, 0], ![67, 0, 0, 1, 0, 0, 0, 0], ![47, 0, 0, 0, 1, 0, 0, 0], ![39, 0, 0, 0, 0, 1, 0, 0], ![56, 0, 0, 0, 0, 0, 1, 0], ![54, 0, 0, 0, 0, 0, 0, 1]] ![-82, 5, -6, 5, -5, 3, -3, 5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A3
 g := ![-5, 5, -6, 5, -5, 3, -3, 5]
 hmem := by decide

def Log34: DiscreteLogCertificate N3 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 0 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2, 5, -6, 5, -5, 3, -3, 5]
 hxeq :=  rfl
 m := 84
 C := ![-82, 5, -6, 5, -5, 3, -3, 5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log34Mem
 k := 80
 hpow := by zmod_pow
 heql := by decide

def Log40Mem : IdealMemCertificate B I4
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![30, 1, 0, 0, 0, 0, 0, 0], ![9, 0, 1, 0, 0, 0, 0, 0], ![33, 0, 0, 1, 0, 0, 0, 0], ![20, 0, 0, 0, 1, 0, 0, 0], ![6, 0, 0, 0, 0, 1, 0, 0], ![22, 0, 0, 0, 0, 0, 1, 0], ![64, 0, 0, 0, 0, 0, 0, 1]] ![-21, 2, -2, 2, -3, 2, -4, 8] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-5, 2, -2, 2, -3, 2, -4, 8]
 hmem := by decide

def Log40: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 zeta1 0 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, 2, -2, 2, -3, 2, -4, 8]
 hxeq :=  rfl
 m := 22
 C := ![-21, 2, -2, 2, -3, 2, -4, 8]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log40Mem
 k := 14
 hpow := by zmod_pow
 heql := by decide

def Log41Mem : IdealMemCertificate B I4
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![30, 1, 0, 0, 0, 0, 0, 0], ![9, 0, 1, 0, 0, 0, 0, 0], ![33, 0, 0, 1, 0, 0, 0, 0], ![20, 0, 0, 0, 1, 0, 0, 0], ![6, 0, 0, 0, 0, 1, 0, 0], ![22, 0, 0, 0, 0, 0, 1, 0], ![64, 0, 0, 0, 0, 0, 0, 1]] ![-71, 1, 0, 0, 0, 0, 0, 0] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-1, 1, 0, 0, 0, 0, 0, 0]
 hmem := by decide

def Log41: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 zeta2 0 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![0, 1, 0, 0, 0, 0, 0, 0]
 hxeq :=  rfl
 m := 71
 C := ![-71, 1, 0, 0, 0, 0, 0, 0]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log41Mem
 k := 44
 hpow := by zmod_pow
 heql := by decide

def Log42Mem : IdealMemCertificate B I4
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![30, 1, 0, 0, 0, 0, 0, 0], ![9, 0, 1, 0, 0, 0, 0, 0], ![33, 0, 0, 1, 0, 0, 0, 0], ![20, 0, 0, 0, 1, 0, 0, 0], ![6, 0, 0, 0, 0, 1, 0, 0], ![22, 0, 0, 0, 0, 0, 1, 0], ![64, 0, 0, 0, 0, 0, 0, 1]] ![-3, -1, 0, 0, 0, 0, 2, -5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![3, -1, 0, 0, 0, 0, 2, -5]
 hmem := by decide

def Log42: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 zeta3 0 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![1, -1, 0, 0, 0, 0, 2, -5]
 hxeq :=  rfl
 m := 4
 C := ![-3, -1, 0, 0, 0, 0, 2, -5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log42Mem
 k := 2
 hpow := by zmod_pow
 heql := by decide

def Log43Mem : IdealMemCertificate B I4
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![30, 1, 0, 0, 0, 0, 0, 0], ![9, 0, 1, 0, 0, 0, 0, 0], ![33, 0, 0, 1, 0, 0, 0, 0], ![20, 0, 0, 0, 1, 0, 0, 0], ![6, 0, 0, 0, 0, 1, 0, 0], ![22, 0, 0, 0, 0, 0, 1, 0], ![64, 0, 0, 0, 0, 0, 0, 1]] ![-11, -5, 5, -5, 5, -3, 5, -10] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![7, -5, 5, -5, 5, -3, 5, -10]
 hmem := by decide

def Log43: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 v 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![-1, -5, 5, -5, 5, -3, 5, -10]
 hxeq :=  rfl
 m := 10
 C := ![-11, -5, 5, -5, 5, -3, 5, -10]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log43Mem
 k := 25
 hpow := by zmod_pow
 heql := by decide

def Log44Mem : IdealMemCertificate B I4
 ![![101, 0, 0, 0, 0, 0, 0, 0], ![30, 1, 0, 0, 0, 0, 0, 0], ![9, 0, 1, 0, 0, 0, 0, 0], ![33, 0, 0, 1, 0, 0, 0, 0], ![20, 0, 0, 0, 1, 0, 0, 0], ![6, 0, 0, 0, 0, 1, 0, 0], ![22, 0, 0, 0, 0, 0, 1, 0], ![64, 0, 0, 0, 0, 0, 0, 1]] ![-72, 5, -6, 5, -5, 3, -3, 5] where
 hieq := ideal_eq_of_IdealEqSpanCertificate' timesTableT_eq_Table rfl A4
 g := ![-5, 5, -6, 5, -5, 3, -3, 5]
 hmem := by decide

def Log44: DiscreteLogCertificate N4 ((orderOf_of_IsOrderOf R101) ▸ IsPrimitiveRoot.orderOf _) 2 alpha0 1 where
 r := 8
 hN := by infer_instance
 hpdvd := by decide
 B := B
 hone := B_one
 xcoord := ![2, 5, -6, 5, -5, 3, -3, 5]
 hxeq :=  rfl
 m := 74
 C := ![-72, 5, -6, 5, -5, 3, -3, 5]
 hCeq := by rfl
 hmem := mem_of_certificate _ _ _ _ Log44Mem
 k := 57
 hpow := by zmod_pow
 heql := by decide

end Sat2
