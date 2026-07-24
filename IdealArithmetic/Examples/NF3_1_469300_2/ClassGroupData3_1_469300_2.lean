import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_469300_2.RI3_1_469300_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-79, -4, 1]

def alpha1 := B.equivFun.symm ![-61, -6, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![121, 12, -2]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0], ![-63, -6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -1104, -460], ![0, -782, 0]], ![![0, 0, 0], ![3422, -9, 0]]], ![![![0, 36061, 15026], ![0, 25546, 0]], ![![0, 0, 0], ![-111783, 294, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![0, 0, 0]], ![![32, 4, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0], ![-63, -6, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![-61, -6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![-126, -12, 2], ![317, 26, -5]]]
 hmul := by decide
 f := ![![![![424, 181, 44], ![-212, -98, 0]], ![![0, 0, 0], ![-4, 0, 0]]], ![![![-6466, -2770, -679], ![3233, 1511, 0]], ![![0, 0, 0], ![61, 0, 0]]]]
 g := ![![![![43, -6, 0], ![-72, -12, 0]], ![![11, -1, 0], ![-18, -3, 0]]], ![![![-163, 288, -18], ![2234, 360, 0]], ![![450, -727, 45], ![-5657, -912, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0], ![-61, -6, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![-63, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![-122, -12, 2], ![319, 28, -5]]]
 hmul := by decide
 f := ![![![![130556586, 57247506, 13377960], ![-65278292, -29965559, 0]], ![![6385920, 0, 0], ![-13304, 7, 0]]], ![![![-2219412908, -973186106, -227420298], ![1109706456, 509403253, 0]], ![![-108558240, 0, 0], ![226163, -119, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![1, -1, 0], ![2, 0, 0]], ![![1, 2, 0], ![-5, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0], ![-63, -4, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![8, 0, 0], ![-59, -8, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![-126, -8, 2], ![317, 28, -3]]]
 hmul := by decide
 f := ![![![![80560, 33572, 8631], ![-40280, -19176, 0]], ![![3816, 0, 0], ![-8, 0, 0]]], ![![![-594130, -247601, -63660], ![297065, 141436, 0]], ![![-28143, 0, 0], ![59, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![38, -8, -2], ![-40, -7, 0]]], ![![![42, 34, 2], ![98, 14, 0]], ![![103, -83, -11], ![-307, -49, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![8, 0, 0], ![-59, -8, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![8, 0, 0], ![-63, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![16, 0, 0], ![8, 8, 0]], ![![-118, -16, 2], ![321, 28, -7]]]
 hmul := by decide
 f := ![![![![192729880, 88920171, 18792682], ![-96364940, -42508513, 0]], ![![19272988, 0, 0], ![-119708, 45, 0]]], ![![![-1477598430, -681722551, -144077492], ![738799215, 325899195, 0]], ![![-147759843, 0, 0], ![917763, -345, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![1, -1, 0], ![2, 0, 0]], ![![48, 4, -1], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![8, 0, 0], ![-63, -4, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![16, 0, 0], ![-181, -20, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![16, 0, 0], ![8, 8, 0]], ![![-126, -8, 2], ![317, 28, -3]]]
 hmul := by decide
 f := ![![![![27136, 11312, 2907], ![-13568, -6456, 0]], ![![2544, 0, 0], ![-16, 0, 0]]], ![![![-306976, -127978, -32895], ![153488, 73053, 0]], ![![-28779, 0, 0], ![181, 0, 0]]]]
 g := ![![![![225, -140, -12], ![-736, -120, 0]], ![![175, -42, -6], ![-268, -45, 0]]], ![![![-590, 1212, 74], ![5806, 930, 0]], ![![1724, -3002, -189], ![-14493, -2325, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![16, 0, 0], ![-181, -20, 3]] ![![2, 0, 0], ![1, 1, 0]]
  ![![16, 0, 0], ![-63, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![32, 0, 0], ![16, 16, 0]], ![![-362, -40, 6], ![959, 84, -17]]]
 hmul := by decide
 f := ![![![![21788636160, 9720053532, 2197006384], ![-10894318080, -4935788120, 0]], ![![1441895040, 0, 0], ![-1001316, 155, 0]]], ![![![-87154522880, -38880204424, -8788023345], ![43577261440, 19743147557, 0]], ![![-5767578720, 0, 0], ![4005263, -620, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![1, -1, 0], ![6, 0, 0]], ![![56, 5, -1], ![-1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![16, 0, 0], ![-63, -4, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![32, 0, 0], ![819, 68, -13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![32, 0, 0], ![16, 16, 0]], ![![-126, -8, 2], ![317, 28, -3]]]
 hmul := by decide
 f := ![![![![27136, 11312, 2907], ![-13568, -6456, 0]], ![![5088, 0, 0], ![-32, 0, 0]]], ![![![694512, 289539, 74421], ![-347256, -165274, 0]], ![![130221, 0, 0], ![-819, 0, 0]]]]
 g := ![![![![-623, 84, 252], ![4512, 744, 0]], ![![-695, 5, 122], ![2084, 341, 0]]], ![![![-1399, -648, -926], ![-17522, -2914, 0]], ![![861, 1407, 2367], ![44095, 7316, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ08 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![819, 68, -13]] ![![2, 0, 0], ![1, 1, 0]]
  ![![32, 0, 0], ![-47, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := rfl
 M := ![![![64, 0, 0], ![32, 32, 0]], ![![1638, 136, -26], ![-4121, -348, 55]]]
 hmul := by decide
 f := ![![![![5094565828608, 2184941176084, 533407140989], ![-2547282914304, -1188108755765, 0]], ![![-149254858260, 0, 0], ![14483732, -693, 0]]], ![![![-7410277728768, -3178096324694, -775864949089], ![3705138864384, 1728158227493, 0]], ![![217097980335, 0, 0], ![-21067247, 1008, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![60, 5, -1], ![6, 0, 0]], ![![-1, 0, -1], ![87, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ09 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![-47, -4, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![64, 0, 0], ![-1213, -108, 19]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![64, 0, 0], ![32, 32, 0]], ![![-94, -8, 2], ![333, 44, -3]]]
 hmul := by decide
 f := ![![![![21376, 9222, 2161], ![-10688, -4996, 0]], ![![10688, 0, 0], ![-64, 0, 0]]], ![![![-405142, -174791, -40961], ![202571, 94697, 0]], ![![-202571, 0, 0], ![1213, 0, 0]]]]
 g := ![![![![1959, -2628, 250], ![-20896, -3528, 0]], ![![1681, -1201, 109], ![-10036, -1701, 0]]], ![![![-892, 4024, -397], ![30702, 5166, 0]], ![![7310, -13861, 1339], ![-108361, -18270, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ010 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![64, 0, 0], ![-1213, -108, 19]] ![![2, 0, 0], ![1, 1, 0]]
  ![![-79, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := rfl
 M := ![![![128, 0, 0], ![64, 64, 0]], ![![-2426, -216, 38], ![6007, 484, -89]]]
 hmul := by decide
 f := ![![![![-93260062821528, -40344742143681, -9706592244049], ![46630031410764, 21604364216900, 0]], ![![-3690146370636, 0, 0], ![111673719, -3302, 0]]]]
 g := ![![![![8, 2, 0]], ![![4, 5, 1]]], ![![![74, 5, -1]], ![![-153, -8, 2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow12 : J0 ^ 12 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 0, 0], ![-1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![6, 0, 0], ![-1, 1, 0]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![18, 0, 0], ![-61, -6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![36, 0, 0], ![-6, 6, 0]], ![![-6, 6, 0], ![1, -2, 1]]]
 hmul := by decide
 f := ![![![![0, 111995214, -47525486], ![0, -26586782, 0]], ![![0, 0, 0], ![1860645318, -4896435, 0]]], ![![![0, -370212739, 157100823], ![0, 87885594, 0]], ![![0, 0, 0], ![-6150571761, 16185715, 0]]]]
 g := ![![![![2581, -30, -23], ![-8658, -1512, 0]], ![![-473, 9, 4], ![1692, 294, 0]]], ![![![-473, 9, 4], ![1692, 294, 0]], ![![108, 0, -1], ![-317, -56, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![18, 0, 0], ![-61, -6, 1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![-61, -6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![108, 0, 0], ![-18, 18, 0]], ![![-366, -36, 6], ![441, 40, -7]]]
 hmul := by decide
 f := ![![![![-299412649499210, 154615855643341, -1753047670380], ![-983784419783114, 23840624364251, 0]], ![![-39929928071117, 6170572365, 0], ![54445885, -61, 0]]]]
 g := ![![![![-8, -7, -1]], ![![-62, -16, -1]]], ![![![6, 0, 0]], ![![-1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![201, 68, 6])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![18, 0, 0], ![-61, -6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![1, 1, 0]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![6, 0, 0], ![-61, -6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![12, 0, 0], ![-2, 2, 0]], ![![6, 6, 0], ![-1, 0, 1]]]
 hmul := by decide
 f := ![![![![0, 1024, 3756], ![0, 457, 0]], ![![0, 0, 0], ![-45986, -121, 0]]], ![![![0, -10889, -39953], ![0, -4842, 0]], ![![0, 0, 0], ![489121, 1287, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![2, 0, 0], ![-6, -1, 0]]], ![![![8, 0, 0], ![-18, -3, 0]], ![![10, 1, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![-61, -6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![1, 1, 0]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![36, 0, 0], ![-61, -6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![36, 0, 0], ![-122, -12, 2]], ![![18, 18, 0], ![319, 28, -5]]]
 hmul := by decide
 f := ![![![![2765067, -33822, -24488], ![-9360522, -1633536, 0]], ![![-1512, 0, 0], ![-36, 0, 0]]], ![![![-4696080, 57447, 41589], ![15897759, 2774368, 0]], ![![2571, 0, 0], ![61, 0, 0]]]]
 g := ![![![![1492, 96, -21], ![-2484, -540, 0]], ![![-4848, -308, 68], ![8354, 1800, 0]]], ![![![637, 42, -9], ![-1026, -225, 0]], ![![12814, 818, -180], ![-21815, -4715, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![36, 0, 0], ![-61, -6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-63, -6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![2, 0, 0], ![-63, -6, 1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![12, 0, 0], ![-61, -6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![12, 0, 0], ![-2, 2, 0]], ![![-378, -36, 6], ![443, 38, -7]]]
 hmul := by decide
 f := ![![![![982, -512, 5], ![3228, -72, 0]], ![![0, 0, 0], ![-12, 0, 0]]], ![![![-4988, 2603, -30], ![-16386, 394, 0]], ![![0, 0, 0], ![61, 0, 0]]]]
 g := ![![![![524, -60, -1], ![-2364, -396, 0]], ![![-90, 13, 0], ![462, 77, 0]]], ![![![-14628, 2016, 5], ![73602, 12276, 0]], ![![17240, -2360, -7], ![-86383, -14410, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![-61, -6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![2, 0, 0], ![-63, -6, 1]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![36, 0, 0], ![-75, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![36, 0, 0], ![-122, -12, 2]], ![![-1134, -108, 18], ![-717, -16, 7]]]
 hmul := by decide
 f := ![![![![2092395, -26154, -18536], ![-7083054, -1236096, 0]], ![![0, 0, 0], ![36, 0, 0]]], ![![![-4358967, 54500, 38614], ![14756219, 2575168, 0]], ![![0, 0, 0], ![-75, 0, 0]]]]
 g := ![![![![26061, 1292, 44], ![-54432, -13212, 0]], ![![-88227, -4374, -150], ![184462, 44765, 0]]], ![![![-820704, -40690, -1386], ![1714302, 416097, 0]], ![![-518957, -25728, -877], ![1084087, 263127, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![36, 0, 0], ![-75, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-61, -6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![4, 0, 0], ![-61, -6, 1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![12, 0, 0], ![-63, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![24, 0, 0], ![-4, 4, 0]], ![![-366, -36, 6], ![441, 40, -7]]]
 hmul := by decide
 f := ![![![![23288033190, -12025930462, 136352672], ![76517823340, -1854291672, 0]], ![![689567736, 0, 0], ![-1040072, 391, 0]]], ![![![-124659444118, 64374084071, -729887674], ![-409595316383, 9925912063, 0]], ![![-3691214709, 0, 0], ![5567443, -2093, 0]]]]
 g := ![![![![69, 20, 3], ![-132, -24, 0]], ![![20, -1, -1], ![28, 4, 0]]], ![![![-375, -265, -56], ![2142, 366, 0]], ![![483, 321, 67], ![-2575, -441, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![-63, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![4, 0, 0], ![-61, -6, 1]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![72, 0, 0], ![-1295, -160, 21]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![72, 0, 0], ![-244, -24, 4]], ![![-1098, -108, 18], ![-839, -28, 9]]]
 hmul := by decide
 f := ![![![![199241636837016, -2486028653064, -1765431420053], ![-674477172586512, -117707553623520, 0]], ![![2135730240, -208152, 0], ![72, 0, 0]]], ![![![-3583314215452471, 44710643588259, 31750870974104], ![12130314119558202, 2116942808045700, 0]], ![![-38410608600, 3743565, 0], ![-1295, 0, 0]]]]
 g := ![![![![1646, -3800, -455], ![-6120, -1008, 0]], ![![-2467, 13238, 1489], ![20876, 3410, 0]]], ![![![-11749, 59491, 6711], ![93906, 15345, 0]], ![![-8872, 45526, 5132], ![71845, 11739, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![72, 0, 0], ![-1295, -160, 21]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-63, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![4, 0, 0], ![-63, -4, 1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![24, 0, 0], ![-571, -56, 9]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![24, 0, 0], ![-4, 4, 0]], ![![-378, -24, 6], ![443, 36, -5]]]
 hmul := by decide
 f := ![![![![557478, -296429, 3162], ![1831716, -42978, 0]], ![![15984, 0, 0], ![-24, 0, 0]]], ![![![-13263308, 7052527, -75241], ![-43579440, 1022591, 0]], ![![-380286, 0, 0], ![571, 0, 0]]]]
 g := ![![![![867, -2280, -110], ![-6576, -1104, 0]], ![![4, 444, 18], ![1240, 207, 0]]], ![![![-7837, 36184, 1629], ![102990, 17250, 0]], ![![9560, -42272, -1911], ![-120413, -20171, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0], ![-571, -56, 9]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![4, 0, 0], ![-63, -4, 1]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![72, 0, 0], ![-39, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![72, 0, 0], ![-244, -24, 4]], ![![-1134, -72, 18], ![43, 52, -5]]]
 hmul := by decide
 f := ![![![![460492558, -5748312, -4080279], ![-1558868580, -272048688, 0]], ![![4752, 0, 0], ![-72, 0, 0]]], ![![![-249433373, 3113672, 2210150], ![844386964, 147359672, 0]], ![![-2574, 0, 0], ![39, 0, 0]]]]
 g := ![![![![1141380, 183456, -6869], ![-628488, -280764, 0]], ![![-3867080, -621568, 23271], ![2129576, 951271, 0]]], ![![![-17973867, -2888992, 108163], ![9897930, 4421412, 0]], ![![679857, 109274, -4092], ![-374301, -167230, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![72, 0, 0], ![-39, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-59, -8, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![8, 0, 0], ![-59, -8, 1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![24, 0, 0], ![-63, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![48, 0, 0], ![-8, 8, 0]], ![![-354, -48, 6], ![439, 44, -9]]]
 hmul := by decide
 f := ![![![![76737879032, -38369904821, 464392636], ![252138745392, -6317263592, 0]], ![![4703289360, 0, 0], ![-3054084, 893, 0]]], ![![![-197902978956, 98953978950, -1197644337], ![-650252645136, 16291892617, 0]], ![![-12129537420, 0, 0], ![7876323, -2303, 0]]]]
 g := ![![![![132, 24, 2], ![-240, -48, 0]], ![![20, -1, -1], ![56, 8, 0]]], ![![![-690, -161, -19], ![1878, 354, 0]], ![![887, 201, 23], ![-2317, -439, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0], ![-63, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![8, 0, 0], ![-59, -8, 1]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![144, 0, 0], ![229, 68, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![144, 0, 0], ![-488, -48, 8]], ![![-1062, -144, 18], ![-1721, -108, 23]]]
 hmul := by decide
 f := ![![![![9227954591947, -115121032950, -81766585284], ![-31238681694066, -5451709173120, 0]], ![![99851184, -29160, 0], ![144, 0, 0]]], ![![![14715309586913, -183577153852, -130388658107], ![-49814600585263, -8693539555400, 0]], ![![159227169, -46500, 0], ![229, 0, 0]]]]
 g := ![![![![5081, -2588, -836], ![7200, 2088, 0]], ![![-17833, 8576, 2839], ![-23984, -7070, 0]]], ![![![-38618, 18710, 6174], ![-52290, -15381, 0]], ![![-62439, 30394, 10009], ![-84905, -24941, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![144, 0, 0], ![229, 68, -3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl

lemma PowJ0_6J1_0 : J0 ^ 6*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-63, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
def MulR61_J0_6J1_1 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) J1
  ![![8, 0, 0], ![-63, -4, 1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![48, 0, 0], ![-433, -36, 7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![48, 0, 0], ![-8, 8, 0]], ![![-378, -24, 6], ![443, 36, -5]]]
 hmul := by decide
 f := ![![![![1299472, -690981, 7368], ![4269696, -100182, 0]], ![![74592, 0, 0], ![-48, 0, 0]]], ![![![-11722312, 6233223, -66473], ![-38516166, 903771, 0]], ![![-672882, 0, 0], ![433, 0, 0]]]]
 g := ![![![![6619, 2844, 1374], ![-61632, -10152, 0]], ![![-785, -458, -241], ![10596, 1739, 0]]], ![![![-51726, -22332, -10806], ![484530, 79806, 0]], ![![60959, 26190, 12652], ![-567527, -93483, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_1 : J0 ^ 6*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![48, 0, 0], ![-433, -36, 7]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR61_J0_6J1_1]
 rfl
def MulR62_J0_6J1_2 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![8, 0, 0], ![-63, -4, 1]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![144, 0, 0], ![-111, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![144, 0, 0], ![-488, -48, 8]], ![![-1134, -72, 18], ![43, 52, -5]]]
 hmul := by decide
 f := ![![![![316323573, -3947958, -2802842], ![-1070825022, -186878160, 0]], ![![3168, 0, 0], ![-144, 0, 0]]], ![![![-243832663, 3043220, 2160523], ![825427430, 144051880, 0]], ![![-2442, 0, 0], ![111, 0, 0]]]]
 g := ![![![![23730, -2092, -271], ![-18144, -14292, 0]], ![![-80151, 7097, 916], ![61804, 48425, 0]]], ![![![-186408, 16488, 2130], ![143442, 112536, 0]], ![![7095, -622, -81], ![-5373, -4258, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_2 : J0 ^ 6*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![144, 0, 0], ![-111, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR62_J0_6J1_2]
 rfl

lemma PowJ0_7J1_0 : J0 ^ 7*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![-181, -20, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
def MulR71_J0_7J1_1 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![-181, -20, 3]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![48, 0, 0], ![-63, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![96, 0, 0], ![-16, 16, 0]], ![![-1086, -120, 18], ![1321, 124, -23]]]
 hmul := by decide
 f := ![![![![591233302470, -302157585517, 3499188130], ![1942623708116, -47596088133, 0]], ![![23599648628, 0, 0], ![-35702948, 4085, 0]]], ![![![-769978262466, 393507557365, -4557082265], ![-2529928576672, 61985603809, 0]], ![![-30734426443, 0, 0], ![46496863, -5320, 0]]]]
 g := ![![![![321, 36, -1], ![-336, -96, 0]], ![![-43, -5, 0], ![64, 16, 0]]], ![![![-3147, -379, 4], ![4170, 1086, 0]], ![![3835, 461, -5], ![-5067, -1321, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_1 : J0 ^ 7*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![48, 0, 0], ![-63, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR71_J0_7J1_1]
 rfl
def MulR72_J0_7J1_2 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![16, 0, 0], ![-181, -20, 3]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![288, 0, 0], ![4473, 524, -71]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![288, 0, 0], ![-976, -96, 16]], ![![-3258, -360, 54], ![-3399, -164, 41]]]
 hmul := by decide
 f := ![![![![66532563531935255, -830198447432862, -589524285571624], ![-225227483836056810, -39306356994279744, 0]], ![![230767993440, -7497288, 0], ![288, 0, 0]]], ![![![1033324867863502305, -12893907215558896, -9155969229988042], ![-3498033859200570710, -610471534406069032, 0]], ![![3584084148720, -116441239, 0], ![4473, 0, 0]]]]
 g := ![![![![618856875, -2538634764, -291159746], ![5064510816, 846248616, 0]], ![![-2097243258, 8603145268, 986707568], ![-17163053944, -2867840858, 0]]], ![![![-7000826346, 28718285466, 3293742666], ![-57292240230, -9573181191, 0]], ![![-7303810237, 29961169062, 3436290791], ![-59771760811, -9987493827, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_2 : J0 ^ 7*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![288, 0, 0], ![4473, 524, -71]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR72_J0_7J1_2]
 rfl

lemma PowJ0_8J1_0 : J0 ^ 8*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![-63, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
def MulR81_J0_8J1_1 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![-63, -4, 1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![96, 0, 0], ![2425, 236, -39]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![96, 0, 0], ![-16, 16, 0]], ![![-378, -24, 6], ![443, 36, -5]]]
 hmul := by decide
 f := ![![![![557478, -296429, 3162], ![1831716, -42978, 0]], ![![63936, 0, 0], ![-96, 0, 0]]], ![![![14082104, -7487907, 79885], ![46269774, -1085714, 0]], ![![1615050, 0, 0], ![-2425, 0, 0]]]]
 g := ![![![![8701, -41548, 472], ![152928, 25080, 0]], ![![-2071, 7025, -71], ![-26044, -4275, 0]]], ![![![-41968, 162604, -1731], ![-600978, -98610, 0]], ![![46358, -190761, 2073], ![704147, 115520, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_1 : J0 ^ 8*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![96, 0, 0], ![2425, 236, -39]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR81_J0_8J1_1]
 rfl
def MulR82_J0_8J1_2 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![16, 0, 0], ![-63, -4, 1]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![288, 0, 0], ![-111, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![288, 0, 0], ![-976, -96, 16]], ![![-1134, -72, 18], ![43, 52, -5]]]
 hmul := by decide
 f := ![![![![641682818, -8008080, -5685739], ![-2172238092, -379095696, 0]], ![![6336, 0, 0], ![-288, 0, 0]]], ![![![-247315129, 3086453, 2191377], ![837216580, 146109764, 0]], ![![-2442, 0, 0], ![111, 0, 0]]]]
 g := ![![![![19511895, -1047620, -209778], ![-7506288, -16980588, 0]], ![![-66122459, 3550222, 710902], ![25438124, 57544471, 0]]], ![![![-76827126, 4124972, 825991], ![29556306, 66860424, 0]], ![![2912778, -156384, -31316], ![-1120329, -2534833, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_2 : J0 ^ 8*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![288, 0, 0], ![-111, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR82_J0_8J1_2]
 rfl

lemma PowJ0_9J1_0 : J0 ^ 9*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![819, 68, -13]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07]
 rfl     
def MulR91_J0_9J1_1 : IdealMulEqCertificate timesTableO (((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![819, 68, -13]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![96, 0, 0], ![-15, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := rfl
 M := ![![![192, 0, 0], ![-32, 32, 0]], ![![4914, 408, -78], ![-5759, -484, 81]]]
 hmul := by decide
 f := ![![![![33528860700632, -17540316792129, 197872344991], ![110166256587792, -2631778593914, 0]], ![![-592603119360, 0, 0], ![29394996, -955, 0]]], ![![![-6705767349472, 3508060852239, -39574440727], ![-22033235576832, 526355342757, 0]], ![![118520539200, 0, 0], ![-5878995, 191, 0]]]]
 g := ![![![![747, 156, -7], ![-96, -192, 0]], ![![-122, -25, 1], ![32, 32, 0]]], ![![![19014, 3969, -173], ![-3126, -4914, 0]], ![![-22274, -4649, 202], ![3725, 5759, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_9J1_1 : J0 ^ 9*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![96, 0, 0], ![-15, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR91_J0_9J1_1]
 rfl
def MulR92_J0_9J1_2 : IdealMulEqCertificate timesTableO (((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![32, 0, 0], ![819, 68, -13]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![576, 0, 0], ![7543, 708, -121]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![576, 0, 0], ![-1952, -192, 32]], ![![14742, 1224, -234], ![5521, -132, -31]]]
 hmul := by decide
 f := ![![![![128105401951460945213, -1598629539586561170, -1135098336457931830], ![-433665157785447567726, -75682702992161989152, 0]], ![![-97078405257504, 75293064, 0], ![-576, 0, 0]]], ![![![1677600140442859188366, -20934801337594442899, -14864643486148991703], ![-5679048022359721823572, -991100384797615546740, 0]], ![![-1271287110559667, 985997880, 0], ![-7543, 0, 0]]]]
 g := ![![![![1840797, -2078172, 153520], ![21585888, 3564216, 0]], ![![-6256449, 7038830, -519795], ![-73129976, -12075318, 0]]], ![![![47222511, -53164179, 3926276], ![552322782, 91199889, 0]], ![![17690943, -19916515, 1470870], ![206912971, 34165605, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_9J1_2 : J0 ^ 9*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![576, 0, 0], ![7543, 708, -121]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR92_J0_9J1_2]
 rfl

lemma PowJ0_10J1_0 : J0 ^ 10*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![-47, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08]
 rfl     
def MulR101_J0_10J1_1 : IdealMulEqCertificate timesTableO ((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![-47, -4, 1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![192, 0, 0], ![-3733, -268, 59]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![192, 0, 0], ![-32, 32, 0]], ![![-282, -24, 6], ![427, 52, -5]]]
 hmul := by decide
 f := ![![![![3602770, -1881675, 12780], ![11837676, -284718, 0]], ![![1109376, 0, 0], ![-192, 0, 0]]], ![![![-70047582, 36584837, -248482], ![-230156336, 5535716, 0]], ![![-21569274, 0, 0], ![3733, 0, 0]]]]
 g := ![![![![2820, 432, 31], ![-864, -168, 0]], ![![3224, 192, -64], ![340, 29, 0]]], ![![![87, -330, -112], ![1482, 246, 0]], ![![842, 569, 154], ![-2191, -372, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_10J1_1 : J0 ^ 10*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![192, 0, 0], ![-3733, -268, 59]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR101_J0_10J1_1]
 rfl
def MulR102_J0_10J1_2 : IdealMulEqCertificate timesTableO ((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![32, 0, 0], ![-47, -4, 1]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![576, 0, 0], ![177, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![576, 0, 0], ![-1952, -192, 32]], ![![-846, -72, 18], ![-933, -44, 11]]]
 hmul := by decide
 f := ![![![![509125518573, -6353366022, -4511241170], ![-1723502648718, -300783534480, 0]], ![![6724800, 0, 0], ![576, 0, 0]]], ![![![156450029242, -1952336431, -1386266819], ![-529618001623, -92428273652, 0]], ![![2066475, 0, 0], ![177, 0, 0]]]]
 g := ![![![![103479, 81224, -1246], ![31536, -171540, 0]], ![![-351124, -275245, 4220], ![-105404, 581321, 0]]], ![![![-152172, -119292, 1829], ![-45702, 251946, 0]], ![![-167837, -131560, 2017], ![-50353, 277857, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_10J1_2 : J0 ^ 10*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![576, 0, 0], ![177, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR102_J0_10J1_2]
 rfl

lemma PowJ0_11J1_0 : J0 ^ 11*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64, 0, 0], ![-1213, -108, 19]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09]
 rfl     
def MulR111_J0_11J1_1 : IdealMulEqCertificate timesTableO (((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![64, 0, 0], ![-1213, -108, 19]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![192, 0, 0], ![-15, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := rfl
 M := ![![![384, 0, 0], ![-64, 64, 0]], ![![-7278, -648, 114], ![8433, 700, -127]]]
 hmul := by decide
 f := ![![![![16938876444808820, -8816554738464993, 102738460907197], ![55656308318657552, -1336597207572771, 0]], ![![404302093483668, 0, 0], ![-1682005972, 34853, 0]]], ![![![-1302990498078518, 678196519553082, -7902958545419], ![-4281254493686558, 102815169996673, 0]], ![![-31100161092675, 0, 0], ![129385075, -2681, 0]]]]
 g := ![![![![762, 160, -8], ![0, -384, 0]], ![![-122, -25, 1], ![64, 64, 0]]], ![![![-14349, -3011, 146], ![1194, 7278, 0]], ![![16639, 3492, -170], ![-1219, -8433, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_11J1_1 : J0 ^ 11*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![192, 0, 0], ![-15, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR111_J0_11J1_1]
 rfl
def MulR112_J0_11J1_2 : IdealMulEqCertificate timesTableO (((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![64, 0, 0], ![-1213, -108, 19]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![1152, 0, 0], ![-399, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1152, 0, 0], ![-3904, -384, 64]], ![![-21834, -1944, 342], ![-10367, -4, 81]]]
 hmul := by decide
 f := ![![![![4308916032889611008244, -53770522885661325456, -38179824857567409185], ![-14586635260767215053080, -2545643392663141034208, 0]], ![![2199242933254368, -663625800, 0], ![1152, 0, 0]]], ![![![-1492410970270015308518, 18623644002155408777, 13223740965360598755], ![5052141725745742331440, 881694165448403670524, 0]], ![![-761716927140156, 229849553, 0], ![-399, 0, 0]]]]
 g := ![![![![110562, -98872, -1267], ![-37152, -374184, 0]], ![![-373593, 335072, 4291], ![129032, 1268050, 0]]], ![![![-2090442, 1873958, 24001], ![718650, 7091865, 0]], ![![-992580, 889786, 11396], ![341213, 3367331, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_11J1_2 : J0 ^ 11*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1152, 0, 0], ![-399, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR112_J0_11J1_2]
 rfl
