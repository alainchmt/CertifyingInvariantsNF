import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_331240_2.RI3_1_331240_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![74, -91, 55]

def alpha1 := B.equivFun.symm ![-13, -2, 2]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-1369937, 386290, -176239]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0], ![-2, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![0, -5, 11]]]
 hmul := by decide
 f := ![![![![908, 2466, -6732], ![1233, 1188, 0]], ![![0, 0, 0], ![75, -3, 0]]], ![![![-908, -2504, 6834], ![-1250, -1206, 0]], ![![0, 0, 0], ![-76, 3, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![3, -1, 4], ![3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0], ![-2, -1, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![74, -91, 55]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![-4, -2, 2], ![110, 3, -5]]]
 hmul := by decide
 f := ![![![![3071, 1548, -4250], ![775, 750, 0]], ![![0, 0, 0], ![-111, 0, 0]]]]
 g := ![![![![146966, 8664, 15983]], ![![879065, 51823, 95601]]], ![![![329554, 19428, 35840]], ![![1971200, 116207, 214374]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![9, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![1, -3, 11]]]
 hmul := by decide
 f := ![![![![-18, -15, -11], ![54, 0, 0]], ![![0, 0, 0], ![9, 0, 0]]], ![![![-4870, -5037, -264], ![14610, -734, 0]], ![![0, 0, 0], ![2424, -2, 0]]]]
 g := ![![![![21, 6, -11], ![-45, 9, 0]], ![![7, 3, -11], ![-15, 9, 0]]], ![![![7, 3, -11], ![-15, 9, 0]], ![![-3, -1, 0], ![7, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![9, 0, 0], ![4, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![-13, -2, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![12, 3, 0], ![4, 0, 11]]]
 hmul := by decide
 f := ![![![![-828540, -789804, 14065], ![2325471, -66, 0]], ![![116472, -14553, 0], ![9706, 4, 0]]]]
 g := ![![![![-239, -14, -26]], ![![-1033, -61, -112]]], ![![![-424, -25, -46]], ![![-1828, -108, -199]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![5987053215037, 352951210200, 651110281747])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![6, 0, 0], ![-2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![6, 0, 0], ![2, 2, 0]], ![![0, 3, 0], ![0, -4, 11]]]
 hmul := by decide
 f := ![![![![-760, -613, 33], ![2283, -39, 0]], ![![-300, 20, 0], ![0, 0, 0]]], ![![![-6, -5, 0], ![17, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-37, -765, 1232], ![-114, -672, 0]], ![![1, 0, 0], ![2, 0, 0]]], ![![![21, 382, -616], ![63, 336, 0]], ![![-27, -574, 924], ![-81, -503, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![0, 1, 0]] ![![9, 0, 0], ![4, 1, 0]]
  ![![18, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![18, 0, 0], ![8, 2, 0]], ![![0, 9, 0], ![0, -1, 11]]]
 hmul := by decide
 f := ![![![![57, 4193, -154], ![-126, -639, 0]], ![![-7650, 170, 0], ![0, 0, 0]]], ![![![10, 1675, -66], ![-22, -252, 0]], ![![-3061, 68, 0], ![0, 0, 0]]]]
 g := ![![![![-7, 468, -5170], ![36, 8460, 0]], ![![-4, 187, -2068], ![20, 3384, 0]]], ![![![-2, -94, 1034], ![9, -1692, 0]], ![![0, 0, 0], ![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![18, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-2, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![2, 0, 0], ![-2, -1, 1]] ![![3, 0, 0], ![1, 1, 0]]
  ![![6, 0, 0], ![-2, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![6, 0, 0], ![2, 2, 0]], ![![-6, -3, 3], ![108, 2, -4]]]
 hmul := by decide
 f := ![![![![4, 7, -11], ![-9, 3, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![-6, -4, -3], ![14, 1, 0]], ![![-1, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-59, -4, 5], ![-15, 3, 0]], ![![-31, 2, -1], ![16, 2, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![-168, -84, 84], ![-503, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![-2, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![2, 0, 0], ![-2, -1, 1]] ![![9, 0, 0], ![4, 1, 0]]
  ![![18, 0, 0], ![-2, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![18, 0, 0], ![8, 2, 0]], ![![-18, -9, 9], ![102, -1, -1]]]
 hmul := by decide
 f := ![![![![-3, 6, -77], ![9, 63, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![-2, -8, 80], ![2, -65, 0]], ![![-1, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-27, 12, -11], ![243, 9, 0]], ![![62, 2, -3], ![4, -10, 0]]], ![![![0, 0, 0], ![9, 0, 0]], ![![136, 68, -68], ![1228, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![18, 0, 0], ![-2, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
