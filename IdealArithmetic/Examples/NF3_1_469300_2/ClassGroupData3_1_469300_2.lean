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
  ![![8, 0, 0], ![67, 8, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![-126, -8, 2], ![317, 28, -3]]]
 hmul := by decide
 f := ![![![![80560, 33572, 8631], ![-40280, -19176, 0]], ![![3816, 0, 0], ![-8, 0, 0]]], ![![![674690, 281173, 72291], ![-337345, -160612, 0]], ![![31959, 0, 0], ![-67, 0, 0]]]]
 g := ![![![![-66, -8, 1], ![8, 0, 0]], ![![-2, -15, -2], ![40, 7, 0]]], ![![![-61, 24, 5], ![-74, -14, 0]], ![![-3, -108, -14], ![283, 49, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![8, 0, 0], ![67, 8, -1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![8, 0, 0], ![-63, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![16, 0, 0], ![8, 8, 0]], ![![134, 16, -2], ![-313, -20, 7]]]
 hmul := by decide
 f := ![![![![213000434, 96062762, 21466175], ![-106500216, -47735746, 0]], ![![-18794156, 0, 0], ![119708, -45, 0]]], ![![![-1633006298, -736482525, -164574314], ![816503149, 365974731, 0]], ![![144088791, 0, 0], ![-917763, 345, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![1, 1, 0], ![-2, 0, 0]], ![![16, 1, 0], ![7, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![8, 0, 0], ![-63, -4, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![16, 0, 0], ![323, 28, -5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![16, 0, 0], ![8, 8, 0]], ![![-126, -8, 2], ![317, 28, -3]]]
 hmul := by decide
 f := ![![![![27136, 11312, 2907], ![-13568, -6456, 0]], ![![2544, 0, 0], ![-16, 0, 0]]], ![![![547808, 228379, 58701], ![-273904, -130363, 0]], ![![51357, 0, 0], ![-323, 0, 0]]]]
 g := ![![![![39, -92, 10], ![704, 120, 0]], ![![-66, -41, 5], ![268, 45, 0]]], ![![![-585, 688, -73], ![-5442, -930, 0]], ![![534, -1800, 197], ![13651, 2325, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![16, 0, 0], ![323, 28, -5]] ![![2, 0, 0], ![1, 1, 0]]
  ![![16, 0, 0], ![-63, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![32, 0, 0], ![16, 16, 0]], ![![646, 56, -10], ![-1577, -124, 23]]]
 hmul := by decide
 f := ![![![![374104823400, 161281574172, 39090039900], ![-187052411700, -86866604663, 0]], ![![-13895322012, 0, 0], ![1354716, -155, 0]]], ![![![-1496419017450, -645126177638, -156360130747], ![748209508725, 347466354534, 0]], ![![55581277791, 0, 0], ![-5418863, 620, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![64, 5, -1], ![6, 0, 0]], ![![55, 2, -1], ![39, 0, 0]]]]
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
  ![![64, 0, 0], ![-1811, -148, 29]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![64, 0, 0], ![32, 32, 0]], ![![-94, -8, 2], ![333, 44, -3]]]
 hmul := by decide
 f := ![![![![21376, 9222, 2161], ![-10688, -4996, 0]], ![![10688, 0, 0], ![-64, 0, 0]]], ![![![-604874, -260961, -61154], ![302437, 141381, 0]], ![![-302437, 0, 0], ![1811, 0, 0]]]]
 g := ![![![![1699, 2532, 1542], ![-21408, -3528, 0]], ![![1660, 1290, 730], ![-10292, -1701, 0]]], ![![![641, -3452, -2308], ![31458, 5166, 0]], ![![3135, 12650, 8076], ![-111063, -18270, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ010 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![64, 0, 0], ![-1811, -148, 29]] ![![2, 0, 0], ![1, 1, 0]]
  ![![-79, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := rfl
 M := ![![![128, 0, 0], ![64, 64, 0]], ![![-3622, -296, 58], ![9209, 796, -119]]]
 hmul := by decide
 f := ![![![![-129727684872390, -55533657672077, -13592414711359], ![64863842436195, 30300806244479, 0]], ![![-3438012849975, 0, 0], ![149316519, -3302, 0]]]]
 g := ![![![![8, 2, 0]], ![![4, 5, 1]]], ![![![118, 11, -1]], ![![-131, 17, 5]]]]
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
  ![![72, 0, 0], ![-1445, -168, 23]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![72, 0, 0], ![-244, -24, 4]], ![![-1098, -108, 18], ![-839, -28, 9]]]
 hmul := by decide
 f := ![![![![199241636837016, -2486028653064, -1765431420053], ![-674477172586512, -117707553623520, 0]], ![![2135730240, -208152, 0], ![72, 0, 0]]], ![![![-3998387558729995, 49889702749255, 35428734363913], ![13535429533355570, 2362158961592500, 0]], ![![-42859902960, 4177201, 0], ![-1445, 0, 0]]]]
 g := ![![![![4201, -16080, -1800], ![-25920, -4320, 0]], ![![-9712, 54904, 6016], ![87884, 14610, 0]]], ![![![-46594, 246732, 27118], ![395334, 65745, 0]], ![![-35252, 188835, 20743], ![302511, 50305, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![72, 0, 0], ![-1445, -168, 23]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-63, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![4, 0, 0], ![-63, -4, 1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![24, 0, 0], ![-437, -32, 7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![24, 0, 0], ![-4, 4, 0]], ![![-378, -24, 6], ![443, 36, -5]]]
 hmul := by decide
 f := ![![![![557478, -296429, 3162], ![1831716, -42978, 0]], ![![15984, 0, 0], ![-24, 0, 0]]], ![![![-10150728, 5397469, -57584], ![-33352392, 782615, 0]], ![![-291042, 0, 0], ![437, 0, 0]]]]
 g := ![![![![153, 144, 40], ![-576, -96, 0]], ![![155, -12, -10], ![112, 17, 0]]], ![![![-106, -2092, -664], ![9162, 1506, 0]], ![![461, 2474, 772], ![-10707, -1763, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0], ![-437, -32, 7]] i)) := by 
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

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![67, 8, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![8, 0, 0], ![67, 8, -1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![24, 0, 0], ![-63, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![48, 0, 0], ![-8, 8, 0]], ![![402, 48, -6], ![-447, -36, 9]]]
 hmul := by decide
 f := ![![![![88718889824, -44991078705, 598852844], ![291504923712, -7188159711, 0]], ![![-4788803712, 0, 0], ![3054084, -893, 0]]], ![![![-228801379542, 116029640306, -1544410184], ![-751775961348, 18537888179, 0]], ![![12350074464, 0, 0], ![-7876323, 2303, 0]]]]
 g := ![![![![132, 24, 2], ![-240, -48, 0]], ![![20, -1, -1], ![56, 8, 0]]], ![![![822, 185, 21], ![-2118, -402, 0]], ![![-867, -202, -24], ![2373, 447, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0], ![-63, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![8, 0, 0], ![67, 8, -1]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![144, 0, 0], ![4277, 452, -67]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![144, 0, 0], ![-488, -48, 8]], ![![1206, 144, -18], ![1233, 60, -15]]]
 hmul := by decide
 f := ![![![![5838641752051, -72846029262, -51733799196], ![-19765100249730, -3449363914080, 0]], ![![-55492848, 16200, 0], ![-144, 0, 0]]], ![![![173720727667732, -2167433069114, -1539267799420], ![-588083280950903, -102631062941960, 0]], ![![-1651113109, 482010, 0], ![-4277, 0, 0]]]]
 g := ![![![![160720, -1060256, -97549], ![1526832, 257400, 0]], ![![-550024, 3588932, 330350], ![-5168976, -871442, 0]]], ![![![1350710, -8868376, -816096], ![12771738, 2153151, 0]], ![![1382392, -9073295, -834965], ![13066905, 2202915, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![144, 0, 0], ![4277, 452, -67]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl

lemma PowJ0_6J1_0 : J0 ^ 6*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-63, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
def MulR61_J0_6J1_1 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) J1
  ![![8, 0, 0], ![-63, -4, 1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![48, 0, 0], ![-181, -20, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![48, 0, 0], ![-8, 8, 0]], ![![-378, -24, 6], ![443, 36, -5]]]
 hmul := by decide
 f := ![![![![1299472, -690981, 7368], ![4269696, -100182, 0]], ![![74592, 0, 0], ![-48, 0, 0]]], ![![![-4900088, 2605573, -27787], ![-16100286, 377791, 0]], ![![-281274, 0, 0], ![181, 0, 0]]]]
 g := ![![![![317, -20, -8], ![-672, -120, 0]], ![![29, 13, 0], ![140, 21, 0]]], ![![![-1407, 276, 45], ![5562, 942, 0]], ![![1910, -294, -57], ![-6443, -1103, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_1 : J0 ^ 6*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![48, 0, 0], ![-181, -20, 3]] i)) := by 
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

lemma PowJ0_7J1_0 : J0 ^ 7*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![323, 28, -5]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
def MulR71_J0_7J1_1 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![323, 28, -5]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![48, 0, 0], ![-63, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![96, 0, 0], ![-16, 16, 0]], ![![1938, 168, -30], ![-2223, -180, 33]]]
 hmul := by decide
 f := ![![![![38132401571820, -19886984409969, 233303616832], ![125292176593128, -3002018924166, 0]], ![![-854448812640, 0, 0], ![51225948, -4085, 0]]], ![![![-49660802410560, 25899328723507, -303837270658], ![-163171207920408, 3909606069403, 0]], ![![1112770554840, 0, 0], ![-66712863, 5320, 0]]]]
 g := ![![![![321, 36, -1], ![-336, -96, 0]], ![![-43, -5, 0], ![64, 16, 0]]], ![![![5673, 679, -8], ![-7398, -1938, 0]], ![![-6435, -774, 8], ![8541, 2223, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_1 : J0 ^ 7*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![48, 0, 0], ![-63, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR71_J0_7J1_1]
 rfl
def MulR72_J0_7J1_2 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![16, 0, 0], ![323, 28, -5]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![288, 0, 0], ![-6773, -540, 107]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![288, 0, 0], ![-976, -96, 16]], ![![5814, 504, -90], ![2337, -36, -15]]]
 hmul := by decide
 f := ![![![![601458418472387124, -7505600470548624, -5329309941955337], ![-2036069957440793016, -355331830964085216, 0]], ![![-1164523815936, 5238504, 0], ![-288, 0, 0]]], ![![![-14144594695874169185, 176510417585828153, 125330241995958792], ![47882585788044739658, 8356396015364113236, 0]], ![![27386294520481, -123194744, 0], ![6773, 0, 0]]]]
 g := ![![![![119619, 294516, 192238], ![-3274272, -546264, 0]], ![![-401578, -996900, -650934], ![11086184, 1849542, 0]]], ![![![2402068, 5939910, 3877860], ![-66046770, -11018853, 0]], ![![966791, 2389896, 1560217], ![-26573313, -4433337, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_2 : J0 ^ 7*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![288, 0, 0], ![-6773, -540, 107]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR72_J0_7J1_2]
 rfl

lemma PowJ0_8J1_0 : J0 ^ 8*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![-63, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
def MulR81_J0_8J1_1 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![-63, -4, 1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![96, 0, 0], ![-1355, -100, 21]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![96, 0, 0], ![-16, 16, 0]], ![![-378, -24, 6], ![443, 36, -5]]]
 hmul := by decide
 f := ![![![![557478, -296429, 3162], ![1831716, -42978, 0]], ![![63936, 0, 0], ![-96, 0, 0]]], ![![![-7868556, 4183965, -44638], ![-25853826, 606664, 0]], ![![-902430, 0, 0], ![1355, 0, 0]]]]
 g := ![![![![266, 160, 61], ![-1536, -264, 0]], ![![1284, 71, -31], ![356, 45, 0]]], ![![![517, -514, -264], ![6150, 1038, 0]], ![![1478, 756, 277], ![-7057, -1216, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_1 : J0 ^ 8*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![96, 0, 0], ![-1355, -100, 21]] i)) := by 
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
  ![![576, 0, 0], ![-7547, -628, 117]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![576, 0, 0], ![-1952, -192, 32]], ![![14742, 1224, -234], ![5521, -132, -31]]]
 hmul := by decide
 f := ![![![![128105401951460945213, -1598629539586561170, -1135098336457931830], ![-433665157785447567726, -75682702992161989152, 0]], ![![-97078405257504, 75293064, 0], ![-576, 0, 0]]], ![![![-1678490029263846463568, 20945906275672831969, 14872528487912757269], ![5682060493107139446976, 991626117438931825708, 0]], ![![1271961469222783, -986520906, 0], ![7547, 0, 0]]]]
 g := ![![![![1369258, -557632, 291373], ![-17211744, -2939400, 0]], ![![-4616833, 1890914, -987427], ![58310152, 9957850, 0]]], ![![![34921651, -14277085, 7456892], ![-440392878, -75208275, 0]], ![![13083965, -5348851, 2793710], ![-164992823, -28176725, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_9J1_2 : J0 ^ 9*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![576, 0, 0], ![-7547, -628, 117]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR92_J0_9J1_2]
 rfl

lemma PowJ0_10J1_0 : J0 ^ 10*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![-47, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08]
 rfl     
def MulR101_J0_10J1_1 : IdealMulEqCertificate timesTableO ((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![-47, -4, 1]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![192, 0, 0], ![5403, 436, -85]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![192, 0, 0], ![-32, 32, 0]], ![![-282, -24, 6], ![427, 52, -5]]]
 hmul := by decide
 f := ![![![![3602770, -1881675, 12780], ![11837676, -284718, 0]], ![![1109376, 0, 0], ![-192, 0, 0]]], ![![![101384168, -52951482, 359642], ![333119412, -8012174, 0]], ![![31218534, 0, 0], ![-5403, 0, 0]]]]
 g := ![![![![45647271, 85984004, 89899418], ![1440105120, 241165704, 0]], ![![-7612096, -14331072, -14983241], ![-240018500, -40194473, 0]]], ![![![-67052241, -126289588, -132039594], ![-2115153270, -354211986, 0]], ![![101521722, 191225068, 199932380], ![3202731801, 536342170, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_10J1_1 : J0 ^ 10*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![192, 0, 0], ![5403, 436, -85]] i)) := by 
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

lemma PowJ0_11J1_0 : J0 ^ 11*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64, 0, 0], ![-1811, -148, 29]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09]
 rfl     
def MulR111_J0_11J1_1 : IdealMulEqCertificate timesTableO (((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![64, 0, 0], ![-1811, -148, 29]] ![![6, 0, 0], ![-1, 1, 0]]
  ![![192, 0, 0], ![-15, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := rfl
 M := ![![![384, 0, 0], ![-64, 64, 0]], ![![-10866, -888, 174], ![12831, 1092, -177]]]
 hmul := by decide
 f := ![![![![51743967895771414, -27099220914015267, 301367189634243], ![170015894514677508, -4057229965353648, 0]], ![![827225873559360, 0, 0], ![-2344212972, 34853, 0]]], ![![![-3980305227845430, 2084555457591954, -23182091539994], ![-13078145748634980, 312094613118916, 0]], ![![-63632759586000, 0, 0], ![180324075, -2681, 0]]]]
 g := ![![![![762, 160, -8], ![0, -384, 0]], ![![-122, -25, 1], ![64, 64, 0]]], ![![![-21423, -4495, 218], ![1782, 10866, 0]], ![![25308, 5311, -258], ![-1965, -12831, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_11J1_1 : J0 ^ 11*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![192, 0, 0], ![-15, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR111_J0_11J1_1]
 rfl
def MulR112_J0_11J1_2 : IdealMulEqCertificate timesTableO (((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![64, 0, 0], ![-1811, -148, 29]] ![![18, 0, 0], ![-61, -6, 1]]
  ![![1152, 0, 0], ![-399, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1152, 0, 0], ![-3904, -384, 64]], ![![-32598, -2664, 522], ![-11889, 324, 63]]]
 hmul := by decide
 f := ![![![![13498379193203639773130, -168445838888585309220, -119604547600134270751], ![-45695003349982813809660, -7974641269303893132480, 0]], ![![4608849675051360, -761795784, 0], ![1152, 0, 0]]], ![![![-4675219736166922059721, 58341916401609190934, 41425532167373595157], ![15826654329996664671952, 2762050148203917954320, 0]], ![![-1596294240472635, 263851136, 0], ![-399, 0, 0]]]]
 g := ![![![![110562, -98872, -1267], ![-37152, -374184, 0]], ![![-373593, 335072, 4291], ![129032, 1268050, 0]]], ![![![-3121272, 2797806, 35834], ![1072206, 10588113, 0]], ![![-1138269, 1020422, 13069], ![391419, 3861711, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_11J1_2 : J0 ^ 11*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1152, 0, 0], ![-399, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR112_J0_11J1_2]
 rfl
