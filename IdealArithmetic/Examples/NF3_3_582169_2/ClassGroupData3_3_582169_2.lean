import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_582169_2.RI3_3_582169_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-887, 41, 5]

def alpha1 := B.equivFun.symm ![-200, 10, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![181, -8, -1]

def zeta2 := B.equivFun.symm ![-164, 9, 1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![25, 0, 0], ![-12, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-10, 5, 0], ![4, -4, 1]]]
 hmul := by decide
 f := ![![![![-6426225, 3553839, -169228], ![-15819675, 715060, 0]], ![![0, 0, 0], ![655700, 100, 0]]], ![![![3148843, -1741376, 82921], ![7751623, -350376, 0]], ![![0, 0, 0], ![-321292, -49, 0]]]]
 g := ![![![![301, -25, 0], ![625, 0, 0]], ![![-106, 21, -1], ![-220, 25, 0]]], ![![![-106, 21, -1], ![-220, 25, 0]], ![![52, -4, 0], ![108, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![-12, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![125, 0, 0], ![-62, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![-50, 25, 0]], ![![-60, 5, 0], ![24, -14, 1]]]
 hmul := by decide
 f := ![![![![1623601711, -886020967, 33723216], ![4048758965, -164375435, 0]], ![![8196250, -21038000, 0], ![-819625, 500, 0]]], ![![![-808553159, 441238174, -16794152], ![-2016280735, 81858920, 0]], ![![-4081730, 10476918, 0], ![408173, -249, 0]]]]
 g := ![![![![7751, -125, 0], ![15625, 0, 0]], ![![-3026, 111, -1], ![-6100, 125, 0]]], ![![![-3656, 121, -1], ![-7370, 125, 0]], ![![1512, -24, 0], ![3048, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![125, 0, 0], ![-62, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![625, 0, 0], ![188, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![625, 0, 0], ![-250, 125, 0]], ![![-310, 5, 0], ![124, -64, 1]]]
 hmul := by decide
 f := ![![![![204526991875, -110945644865, 4242039749], ![511061346875, -21189560600, 0]], ![![204906250, -515102500, 0], ![-4098125, 2500, 0]]], ![![![61439920803, -33328078468, 1274308999], ![153522859695, -6365345295, 0]], ![![61553850, -154736822, 0], ![-1231077, 751, 0]]]]
 g := ![![![![52265, 278, 0], ![-173750, 0, 0]], ![![-21282, -301, -1], ![70750, 625, 0]]], ![![![-26134, -327, -1], ![86880, 625, 0]], ![![10228, 54, 0], ![-34002, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![625, 0, 0], ![188, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![3125, 0, 0], ![-437, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![3125, 0, 0], ![-1250, 625, 0]], ![![940, 5, 0], ![-376, 186, 1]]]
 hmul := by decide
 f := ![![![![11540675088760627, -6253538533290574, 240435713089478], ![28848798164700005, -1202255239718620, 0]], ![![-3842463471875, 9584267043750, 0], ![81962500, 12500, 0]]], ![![![-1614771117645680, 874995035295805, -33641762041993], ![-4036523487305812, 168219538473061, 0]], ![![537637442104, -1341030527949, 0], ![-11468192, -1749, 0]]]]
 g := ![![![![692646, -1585, 0], ![4953125, 0, 0]], ![![-276534, 1070, -1], ![-1977500, 3125, 0]]], ![![![208450, -477, 0], ![1490630, 0, 0]], ![![-82506, 626, -1], ![-590002, 3126, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![3125, 0, 0], ![-437, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![-887, 41, 5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![15625, 0, 0], ![-6250, 3125, 0]], ![![-2185, 5, 0], ![874, -439, 1]]]
 hmul := by decide
 f := ![![![![37773393909413356, -18931287265930632, 17870533612388], ![94433440502016940, -89250851306358, 0]], ![![126637128450, -63635473729797, 0], ![5883258, -3589, 0]]]]
 g := ![![![![-3813, 144, 29]], ![![-7981, 653, 23]]], ![![![518, -19, -4]], ![![1104, -92, -3]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![41, 0, 0], ![20, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![41, 0, 0], ![20, 1, 0]] ![![41, 0, 0], ![20, 1, 0]]
  ![![-200, 10, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![1681, 0, 0], ![820, 41, 0]], ![![820, 41, 0], ![400, 40, 1]]]
 hmul := by decide
 f := ![![![![-18145413914640, -1597227976702, -34497863678], ![37193714180012, 1414193356559, 0]], ![![0, 0, 0], ![8987300000, -148200, 0]]]]
 g := ![![![![-9195, 505, 56]], ![![-6724, 369, 41]]], ![![![-6724, 369, 41]], ![![-4919, 270, 30]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![163, -9, -1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-10, 1, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![41, 0, 0], ![20, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![-2, 1, 0]] ![![41, 0, 0], ![20, 1, 0]]
  ![![205, 0, 0], ![-62, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![205, 0, 0], ![100, 5, 0]], ![![-82, 41, 0], ![-40, 18, 1]]]
 hmul := by decide
 f := ![![![![136065, 12885, 489], ![-278595, -13325, 0]], ![![410, -820, 0], ![0, 0, 0]]], ![![![-41126, -3909, -149], ![84206, 4059, 0]], ![![-124, 250, 0], ![0, 0, 0]]]]
 g := ![![![![3907, -63, 0], ![12915, 0, 0]], ![![1924, -31, 0], ![6360, 0, 0]]], ![![![-1414, 85, -1], ![-4674, 205, 0]], ![![-720, 74, -1], ![-2380, 206, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![205, 0, 0], ![-62, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![-12, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![-12, 1, 0]] ![![41, 0, 0], ![20, 1, 0]]
  ![![1025, 0, 0], ![-62, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![1025, 0, 0], ![500, 25, 0]], ![![-492, 41, 0], ![-240, 8, 1]]]
 hmul := by decide
 f := ![![![![46672485, 4442393, 108397], ![-95656403, -4370313, 0]], ![![22550, -45100, 0], ![0, 0, 0]]], ![![![-2819006, -268503, -6558], ![5777620, 264368, 0]], ![![-1364, 2750, 0], ![0, 0, 0]]]]
 g := ![![![![16865, -272, 0], ![278800, 0, 0]], ![![8248, -133, 0], ![136350, 0, 0]]], ![![![-7996, 191, -1], ![-132184, 1025, 0]], ![![-3840, 124, -1], ![-63480, 1026, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1025, 0, 0], ![-62, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![125, 0, 0], ![-62, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![125, 0, 0], ![-62, 1, 0]] ![![41, 0, 0], ![20, 1, 0]]
  ![![5125, 0, 0], ![-62, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![5125, 0, 0], ![2500, 125, 0]], ![![-2542, 41, 0], ![-1240, -42, 1]]]
 hmul := by decide
 f := ![![![![6736148265, 641525937, 15277968], ![-13808468187, -625986524, 0]], ![![625250, -1250500, 0], ![0, 0, 0]]], ![![![-81371862, -7754901, -184828], ![166804626, 7572946, 0]], ![![-7564, 15250, 0], ![0, 0, 0]]]]
 g := ![![![![15749, -254, 0], ![1301750, 0, 0]], ![![7752, -125, 0], ![640750, 0, 0]]], ![![![-7750, 187, -1], ![-640584, 5125, 0]], ![![-3720, 60, 0], ![-307480, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5125, 0, 0], ![-62, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![625, 0, 0], ![188, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![625, 0, 0], ![188, 1, 0]] ![![41, 0, 0], ![20, 1, 0]]
  ![![25625, 0, 0], ![10188, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![25625, 0, 0], ![12500, 625, 0]], ![![7708, 41, 0], ![3760, 208, 1]]]
 hmul := by decide
 f := ![![![![-111316744855, -5461376784, 5741741], ![228199374359, -237942967, 0]], ![![-76875, 38591250, 0], ![0, 0, 0]]], ![![![-44257356844, -2171336405, 2282804], ![90727600378, -94601473, 0]], ![![-30564, 15343125, 0], ![0, 0, 0]]]]
 g := ![![![![43186933, 4239, 0], ![-108624375, 0, 0]], ![![21058348, 2067, 0], ![-52966250, 0, 0]]], ![![![12989684, 1275, 0], ![-32671834, 0, 0]], ![![6320528, 620, 0], ![-15897480, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25625, 0, 0], ![10188, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3125, 0, 0], ![-437, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![3125, 0, 0], ![-437, 1, 0]] ![![41, 0, 0], ![20, 1, 0]]
  ![![128125, 0, 0], ![-41062, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![128125, 0, 0], ![62500, 3125, 0]], ![![-17917, 41, 0], ![-8740, -417, 1]]]
 hmul := by decide
 f := ![![![![-2871408564881635, -142792289804473, 41979637836], ![5886387626765633, -1715651901612, 0]], ![![239850000, -420217200000, 0], ![0, 0, 0]]], ![![![920240235257714, 45762630919329, -13453798160], ![-1886492504314236, 549838816768, 0]], ![![-76868064, 134672850000, 0], ![0, 0, 0]]]]
 g := ![![![![5172826513, -125976, 0], ![16140675000, 0, 0]], ![![2523384088, -61453, 0], ![7873668750, 0, 0]]], ![![![-723307117, 58677, -1], ![-2256921834, 128125, 0]], ![![-352832740, 49655, -1], ![-1100937480, 128126, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![128125, 0, 0], ![-41062, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
