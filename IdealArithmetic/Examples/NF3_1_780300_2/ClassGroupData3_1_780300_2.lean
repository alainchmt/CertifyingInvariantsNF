import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_780300_2.RI3_1_780300_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![11, -5, 1]

def alpha1 := B.equivFun.symm ![23, 4, -2]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-1, 49, -14]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![11, 0, 0], ![1, 1, 0]] ![![11, 0, 0], ![1, 1, 0]]
  ![![121, 0, 0], ![-32, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![11, 11, 0]], ![![11, 11, 0], ![1, 2, 2]]]
 hmul := by decide
 f := ![![![![0, -5305, -5152], ![0, -1419, 0]], ![![0, 0, 0], ![329241, -968, 0]]], ![![![0, 1424, 1382], ![0, 391, 0]], ![![0, 0, 0], ![-88432, 260, 0]]]]
 g := ![![![![3233, -101, 0], ![12221, 0, 0]], ![![323, -10, 0], ![1221, 0, 0]]], ![![![323, -10, 0], ![1221, 0, 0]], ![![41, -1, 0], ![155, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![121, 0, 0], ![-32, 1, 0]] ![![11, 0, 0], ![1, 1, 0]]
  ![![11, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![1331, 0, 0], ![121, 121, 0]], ![![-352, 11, 0], ![-32, -31, 2]]]
 hmul := by decide
 f := ![![![![59126, 27418, 559], ![-319807, -2770, 0]], ![![110193, -6993, 0], ![36731, -108, 0]]]]
 g := ![![![![971, 140, 39]], ![![691, 101, 29]]], ![![![-202, -29, -8]], ![![-142, -21, -6]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-4, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![23, 0, 0], ![-4, 1, 0]] ![![23, 0, 0], ![-4, 1, 0]]
  ![![529, 0, 0], ![-142, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![529, 0, 0], ![-92, 23, 0]], ![![-92, 23, 0], ![16, -8, 2]]]
 hmul := by decide
 f := ![![![![-288826383, 76025156, -1904726], ![-1607332092, 8460642, 0]], ![![0, 0, 0], ![308646637, -69828, 0]]], ![![![77579594, -20420573, 511614], ![431734006, -2272543, 0]], ![![0, 0, 0], ![-82903366, 18756, 0]]]]
 g := ![![![![35785, -252, 0], ![133308, 0, 0]], ![![-6100, 185, -2], ![-22724, 529, 0]]], ![![![-6100, 185, -2], ![-22724, 529, 0]], ![![1172, -8, 0], ![4366, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![529, 0, 0], ![-142, 1, 0]] ![![23, 0, 0], ![-4, 1, 0]]
  ![![23, 4, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![12167, 0, 0], ![-2116, 529, 0]], ![![-3266, 23, 0], ![568, -146, 2]]]
 hmul := by decide
 f := ![![![![1294231699667, -911246322635, 2717839646], ![7239262636358, 67213509721, 0]], ![![131240532683, -2264778887203, 0], ![-10159430, -2988, 0]]]]
 g := ![![![![1889, 248, 78]], ![![248, 39, 8]]], ![![![-482, -63, -20]], ![![-64, -10, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-116621, -16709, -4788])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![23, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![529, 0, 0], ![-142, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![11, 0, 0], ![1, 1, 0]] ![![23, 0, 0], ![-4, 1, 0]]
  ![![253, 0, 0], ![111, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![253, 0, 0], ![-44, 11, 0]], ![![23, 23, 0], ![-4, -3, 2]]]
 hmul := by decide
 f := ![![![![7143, -1772, -438], ![39744, -253, 0]], ![![-2530, 2530, 0], ![0, 0, 0]]], ![![![3141, -779, -190], ![17478, -115, 0]], ![![-1110, 1100, 0], ![0, 0, 0]]]]
 g := ![![![![9436, 85, 0], ![-21505, 0, 0]], ![![-1670, -126, -2], ![3806, 253, 0]]], ![![![656, 6, 0], ![-1495, 0, 0]], ![![-172, -2, 0], ![392, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![253, 0, 0], ![111, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![11, 0, 0], ![1, 1, 0]] ![![529, 0, 0], ![-142, 1, 0]]
  ![![5819, 0, 0], ![-142, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![5819, 0, 0], ![-1562, 11, 0]], ![![529, 529, 0], ![-142, -141, 2]]]
 hmul := by decide
 f := ![![![![188566807, -1395348, -9630], ![702458042, -251275, 0]], ![![-58190, 58190, 0], ![0, 0, 0]]], ![![![-4601510, 34109, 236], ![-17141764, 6348, 0]], ![![1420, -1430, 0], ![0, 0, 0]]]]
 g := ![![![![561895, -3957, 0], ![23025783, 0, 0]], ![![-150662, 1203, -2], ![-6173948, 5819, 0]]], ![![![51133, -360, 0], ![2095369, 0, 0]], ![![-13490, 237, -2], ![-552804, 5820, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5819, 0, 0], ![-142, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![-32, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![121, 0, 0], ![-32, 1, 0]] ![![23, 0, 0], ![-4, 1, 0]]
  ![![2783, 0, 0], ![-395, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![2783, 0, 0], ![-484, 121, 0]], ![![-736, 23, 0], ![128, -36, 2]]]
 hmul := by decide
 f := ![![![![374401, -384464, 15022], ![2102016, 43079, 0]], ![![33396, -1135464, 0], ![0, 0, 0]]], ![![![-53133, 54573, -2134], ![-298306, -6095, 0]], ![![-4740, 161172, 0], ![0, 0, 0]]]]
 g := ![![![![1054651, -2670, 0], ![7430610, 0, 0]], ![![-182868, 858, -2], ![-1288408, 2783, 0]]], ![![![-278472, 1100, -2], ![-1961992, 2783, 0]], ![![48636, -123, 0], ![342668, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2783, 0, 0], ![-395, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![121, 0, 0], ![-32, 1, 0]] ![![529, 0, 0], ![-142, 1, 0]]
  ![![64009, 0, 0], ![-5961, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![64009, 0, 0], ![-17182, 121, 0]], ![![-16928, 529, 0], ![4544, -174, 2]]]
 hmul := by decide
 f := ![![![![68599346077, -566719299, 4270266], ![255549718866, -73365423, 0]], ![![7104999, -241569966, 0], ![0, 0, 0]]], ![![![-6388488261, 52777262, -397682], ![-23798716350, 6832564, 0]], ![![-661671, 22496925, 0], ![0, 0, 0]]]]
 g := ![![![![248150470, -41629, 0], ![2664630661, 0, 0]], ![![-66602242, 17134, -2], ![-715172436, 64009, 0]]], ![![![-65624600, 16970, -2], ![-704674552, 64009, 0]], ![![17627216, -2957, 0], ![189280400, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64009, 0, 0], ![-5961, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
