import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_120204_1.RI3_1_120204_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-13, -1, -1]

def alpha1 := B.equivFun.symm ![-35, 4, 2]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-1, -3, 2]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![-2, 1, 0]] ![![7, 0, 0], ![-2, 1, 0]]
  ![![49, 0, 0], ![19, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![-14, 7, 0]], ![![-14, 7, 0], ![4, -4, 3]]]
 hmul := by decide
 f := ![![![![-4023523, 2126336, -169089], ![-13965882, 327327, 0]], ![![0, 0, 0], ![465794, -1176, 0]]], ![![![-1546457, 817267, -64992], ![-5367842, 125814, 0]], ![![0, 0, 0], ![179030, -452, 0]]]]
 g := ![![![![324, 17, 0], ![-833, 0, 0]], ![![-98, -24, -3], ![252, 49, 0]]], ![![![-98, -24, -3], ![252, 49, 0]], ![![-10, -1, 0], ![26, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![19, 1, 0]] ![![7, 0, 0], ![-2, 1, 0]]
  ![![-13, -1, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![-98, 49, 0]], ![![133, 7, 0], ![-38, 17, 3]]]
 hmul := by decide
 f := ![![![![-12010653245, 6300775513, -384735787], ![-41995350920, 912909970, 0]], ![![30864482, -106335256, 0], ![-121994, 308, 0]]]]
 g := ![![![![-1, -9, 4]], ![![38, -1, -5]]], ![![![5, -4, 1]], ![![8, 1, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![2, 1, 0]] ![![11, 0, 0], ![2, 1, 0]]
  ![![121, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![22, 11, 0]], ![![22, 11, 0], ![4, 4, 3]]]
 hmul := by decide
 f := ![![![![-3002473, -1562126, -90063], ![16429688, 284768, 0]], ![![0, 0, 0], ![503481, -847, 0]]], ![![![-24832, -12921, -747], ![135882, 2363, 0]], ![![0, 0, 0], ![4164, -7, 0]]]]
 g := ![![![![119, 59, 0], ![-7139, 0, 0]], ![![18, 9, 0], ![-1078, 0, 0]]], ![![![18, 9, 0], ![-1078, 0, 0]], ![![4, 2, 0], ![-240, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![2, 1, 0]] ![![11, 0, 0], ![2, 1, 0]]
  ![![-35, 4, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![242, 121, 0]], ![![22, 11, 0], ![4, 4, 3]]]
 hmul := by decide
 f := ![![![![-183315583, -95284170, -5439605], ![1007667772, 22742994, 0]], ![![6274324, -30760880, 0], ![-162267, 273, 0]]]]
 g := ![![![![-1969, -228, -142]], ![![-1210, -143, -88]]], ![![![-110, -13, -8]], ![![-68, -8, -5]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-727, -85, -53])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![7, 0, 0], ![-2, 1, 0]] ![![11, 0, 0], ![2, 1, 0]]
  ![![77, 0, 0], ![-9, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![77, 0, 0], ![14, 7, 0]], ![![-22, 11, 0], ![-4, 0, 3]]]
 hmul := by decide
 f := ![![![![13529, 6508, 1002], ![-73678, -1496, 0]], ![![462, -1386, 0], ![0, 0, 0]]], ![![![-1577, -757, -120], ![8588, 176, 0]], ![![-54, 168, 0], ![0, 0, 0]]]]
 g := ![![![![577, -64, 0], ![4928, 0, 0]], ![![118, -13, 0], ![1008, 0, 0]]], ![![![-152, 26, -3], ![-1298, 77, 0]], ![![-26, 3, 0], ![-222, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![77, 0, 0], ![-9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![7, 0, 0], ![-2, 1, 0]] ![![121, 0, 0], ![2, 1, 0]]
  ![![847, 0, 0], ![-240, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![847, 0, 0], ![14, 7, 0]], ![![-242, 121, 0], ![-4, 0, 3]]]
 hmul := by decide
 f := ![![![![1873749, 932292, 5832], ![-113288549, -15609, 0]], ![![4235, -12705, 0], ![0, 0, 0]]], ![![![-530932, -264167, -1656], ![32100626, 4477, 0]], ![![-1200, 3605, 0], ![0, 0, 0]]]]
 g := ![![![![21601, -90, 0], ![76230, 0, 0]], ![![722, -3, 0], ![2548, 0, 0]]], ![![![-5966, 265, -3], ![-21054, 847, 0]], ![![68, 0, 0], ![240, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![847, 0, 0], ![-240, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![19, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![49, 0, 0], ![19, 1, 0]] ![![11, 0, 0], ![2, 1, 0]]
  ![![539, 0, 0], ![68, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![539, 0, 0], ![98, 49, 0]], ![![209, 11, 0], ![38, 21, 3]]]
 hmul := by decide
 f := ![![![![-572128, -331082, 65010], ![3163952, -294635, 0]], ![![-8085, 250635, 0], ![0, 0, 0]]], ![![![-71984, -41666, 8202], ![398088, -37169, 0]], ![![-1020, 31605, 0], ![0, 0, 0]]]]
 g := ![![![![18701, 275, 0], ![-148225, 0, 0]], ![![3326, 49, 0], ![-26362, 0, 0]]], ![![![7207, 106, 0], ![-57123, 0, 0]], ![![1298, 19, 0], ![-10288, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![539, 0, 0], ![68, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![49, 0, 0], ![19, 1, 0]] ![![121, 0, 0], ![2, 1, 0]]
  ![![5929, 0, 0], ![607, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![5929, 0, 0], ![98, 49, 0]], ![![2299, 121, 0], ![38, 21, 3]]]
 hmul := by decide
 f := ![![![![973493264, 484208786, -210618], ![-58891196100, -8298301, 0]], ![![-219373, 6800563, 0], ![0, 0, 0]]], ![![![99664476, 49572432, -21561], ![-6029173922, -849541, 0]], ![![-22459, 696192, 0], ![0, 0, 0]]]]
 g := ![![![![1377284, 2269, 0], ![-13452901, 0, 0]], ![![22454, 37, 0], ![-219324, 0, 0]]], ![![![534148, 880, 0], ![-5217399, 0, 0]], ![![8558, 14, 0], ![-83592, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5929, 0, 0], ![607, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
