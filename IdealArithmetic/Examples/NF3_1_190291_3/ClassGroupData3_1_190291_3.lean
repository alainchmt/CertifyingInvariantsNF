import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_190291_3.RI3_1_190291_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-3, -1, 0]

def alpha1 := B.equivFun.symm ![4, 1, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-10, 1, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![-1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -2, -1], ![0, 0, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![0, -81, -35], ![0, -58, 0]], ![![0, 0, 0], ![258, -1, 0]]]]
 g := ![![![![4, -3, 0], ![12, 0, 0]], ![![1, 1, -1], ![2, 4, 0]]], ![![![1, 1, -1], ![2, 4, 0]], ![![0, 1, 0], ![-1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![-1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![8, 0, 0], ![3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![-2, 2, 0], ![-1, 0, 1]]]
 hmul := by decide
 f := ![![![![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![-8, 0, 0]]], ![![![0, -7, 35], ![0, 14, 0]], ![![0, -37, 0], ![-262, -1, 0]]]]
 g := ![![![![4, 1, 0], ![-8, 0, 0]], ![![2, 1, 0], ![-4, 0, 0]]], ![![![-4, -4, -1], ![10, 8, 0]], ![![1, -3, -1], ![-3, 9, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![3, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![16, 0, 0], ![3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![8, 8, 0]], ![![6, 2, 0], ![3, 4, 1]]]
 hmul := by decide
 f := ![![![![-108, 69, 10], ![56, 94, 0]], ![![224, -448, 0], ![-16, 0, 0]]], ![![![-1748, 1077, 154], ![876, 1491, 0]], ![![3668, -7063, 0], ![-262, -1, 0]]]]
 g := ![![![![22, 7, 0], ![-112, 0, 0]], ![![8, 3, 0], ![-40, 0, 0]]], ![![![6, 2, 0], ![-30, 0, 0]], ![![0, 0, 0], ![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![3, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![32, 0, 0], ![3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![16, 16, 0]], ![![6, 2, 0], ![3, 4, 1]]]
 hmul := by decide
 f := ![![![![-44, 31, 4], ![24, 42, 0]], ![![192, -384, 0], ![-32, 0, 0]]], ![![![-350, 255, 36], ![176, 323, 0]], ![![1572, -3027, 0], ![-262, -1, 0]]]]
 g := ![![![![28, 9, 0], ![-288, 0, 0]], ![![14, 5, 0], ![-144, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![3, 1, 0], ![-31, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![3, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![-3, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![32, 32, 0]], ![![6, 2, 0], ![3, 4, 1]]]
 hmul := by decide
 f := ![![![![1746, -9231, -1319], ![-872, -6147, 0]], ![![-14148, 140427, 0], ![262, 1, 0]]]]
 g := ![![![![65, 3, -1]], ![![-97, -3, 1]]], ![![![-2, 0, 0]], ![![-1, -1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![9, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -761, -388], ![0, -381, 0]], ![![0, 0, 0], ![4671, -18, 0]]], ![![![0, -296, -151], ![0, -148, 0]], ![![0, 0, 0], ![1817, -7, 0]]]]
 g := ![![![![5, 1, 0], ![-9, 0, 0]], ![![-1, 0, 0], ![3, 0, 0]]], ![![![-1, 0, 0], ![3, 0, 0]], ![![-3, -1, 0], ![7, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![9, 0, 0], ![4, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![12, 3, 0], ![4, 5, 1]]]
 hmul := by decide
 f := ![![![![16353, 16353, 12483], ![10902, -34940, 0]], ![![-43608, -6304, 0], ![-3634, -7, 0]]]]
 g := ![![![![-58, -4, 1]], ![![67, 4, -1]]], ![![![3, 0, 0]], ![![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-26, -10, -1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![6, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![6, 0, 0], ![2, 2, 0]], ![![3, 3, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![6, 2, -3], ![-6, 0, 0]], ![![-6, 6, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]]
 g := ![![![![0, -1, 0], ![6, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![1, 1, 0]] ![![9, 0, 0], ![4, 1, 0]]
  ![![18, 0, 0], ![-5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![18, 0, 0], ![8, 2, 0]], ![![9, 9, 0], ![4, 5, 1]]]
 hmul := by decide
 f := ![![![![274, 90, -3], ![-594, -54, 0]], ![![-18, 18, 0], ![0, 0, 0]]], ![![![-81, -27, 1], ![176, 18, 0]], ![![5, -6, 0], ![0, 0, 0]]]]
 g := ![![![![76, -15, 0], ![270, 0, 0]], ![![36, -7, 0], ![128, 0, 0]]], ![![![33, -6, 0], ![117, 0, 0]], ![![18, -3, 0], ![64, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![18, 0, 0], ![-5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![12, 0, 0], ![-5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![12, 0, 0], ![4, 4, 0]], ![![-3, 3, 0], ![-1, 0, 1]]]
 hmul := by decide
 f := ![![![![-14, 28, -29], ![18, 6, 0]], ![![-36, 108, 0], ![0, 0, 0]]], ![![![4, -15, 12], ![-2, 0, 0]], ![![15, -48, 0], ![0, 0, 0]]]]
 g := ![![![![36, -7, 0], ![84, 0, 0]], ![![12, -2, 0], ![28, 0, 0]]], ![![![-4, 6, -1], ![-9, 12, 0]], ![![2, 0, 0], ![5, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![-5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![-1, 1, 0]] ![![9, 0, 0], ![4, 1, 0]]
  ![![36, 0, 0], ![-5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![36, 0, 0], ![16, 4, 0]], ![![-9, 9, 0], ![-4, 3, 1]]]
 hmul := by decide
 f := ![![![![460, 168, 123], ![-972, -378, 0]], ![![108, -324, 0], ![0, 0, 0]]], ![![![-59, -22, -18], ![124, 54, 0]], ![![-15, 48, 0], ![0, 0, 0]]]]
 g := ![![![![156, -31, 0], ![1116, 0, 0]], ![![76, -15, 0], ![544, 0, 0]]], ![![![-34, 12, -1], ![-243, 36, 0]], ![![-14, 3, 0], ![-100, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![36, 0, 0], ![-5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![8, 0, 0], ![3, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![24, 0, 0], ![-5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![24, 0, 0], ![8, 8, 0]], ![![9, 3, 0], ![3, 4, 1]]]
 hmul := by decide
 f := ![![![![104, -102, -37], ![-120, -78, 0]], ![![-168, 504, 0], ![0, 0, 0]]], ![![![-22, 23, 8], ![26, 18, 0]], ![![35, -112, 0], ![0, 0, 0]]]]
 g := ![![![![36, -7, 0], ![168, 0, 0]], ![![12, -2, 0], ![56, 0, 0]]], ![![![21, -4, 0], ![99, 0, 0]], ![![7, -1, 0], ![33, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0], ![-5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![8, 0, 0], ![3, 1, 0]] ![![9, 0, 0], ![4, 1, 0]]
  ![![72, 0, 0], ![-5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![72, 0, 0], ![32, 8, 0]], ![![27, 9, 0], ![12, 7, 1]]]
 hmul := by decide
 f := ![![![![8208, 3274, 269], ![-18162, -3636, 0]], ![![-360, 1080, 0], ![0, 0, 0]]], ![![![-533, -220, -19], ![1178, 261, 0]], ![![25, -80, 0], ![0, 0, 0]]]]
 g := ![![![![166, -33, 0], ![2376, 0, 0]], ![![76, -15, 0], ![1088, 0, 0]]], ![![![66, -13, 0], ![945, 0, 0]], ![![36, -7, 0], ![516, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![72, 0, 0], ![-5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![3, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![48, 0, 0], ![19, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![48, 0, 0], ![16, 16, 0]], ![![9, 3, 0], ![3, 4, 1]]]
 hmul := by decide
 f := ![![![![-132, 699, 184], ![156, 339, 0]], ![![432, -4752, 0], ![0, 0, 0]]], ![![![-52, 275, 72], ![61, 135, 0]], ![![171, -1872, 0], ![0, 0, 0]]]]
 g := ![![![![286, 15, 0], ![-720, 0, 0]], ![![108, 6, 0], ![-272, 0, 0]]], ![![![37, 2, 0], ![-93, 0, 0]], ![![-13, -1, 0], ![33, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![48, 0, 0], ![19, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![16, 0, 0], ![3, 1, 0]] ![![9, 0, 0], ![4, 1, 0]]
  ![![144, 0, 0], ![67, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![144, 0, 0], ![64, 16, 0]], ![![27, 9, 0], ![12, 7, 1]]]
 hmul := by decide
 f := ![![![![-87376, -16852, 919], ![197388, -19854, 0]], ![![-1872, 20592, 0], ![0, 0, 0]]], ![![![-40542, -7812, 428], ![91588, -9234, 0]], ![![-871, 9568, 0], ![0, 0, 0]]]]
 g := ![![![![2212, 33, 0], ![-4752, 0, 0]], ![![864, 13, 0], ![-1856, 0, 0]]], ![![![398, 6, 0], ![-855, 0, 0]], ![![162, 2, 0], ![-348, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![144, 0, 0], ![67, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![3, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![96, 0, 0], ![-29, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![96, 0, 0], ![32, 32, 0]], ![![9, 3, 0], ![3, 4, 1]]]
 hmul := by decide
 f := ![![![![-368, 1942, 511], ![432, 942, 0]], ![![2400, -26400, 0], ![0, 0, 0]]], ![![![110, -590, -155], ![-127, -285, 0]], ![![-725, 8000, 0], ![0, 0, 0]]]]
 g := ![![![![1944, -67, 0], ![6432, 0, 0]], ![![648, -22, 0], ![2144, 0, 0]]], ![![![204, -7, 0], ![675, 0, 0]], ![![68, -2, 0], ![225, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![96, 0, 0], ![-29, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![32, 0, 0], ![3, 1, 0]] ![![9, 0, 0], ![4, 1, 0]]
  ![![288, 0, 0], ![67, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![288, 0, 0], ![128, 32, 0]], ![![27, 9, 0], ![12, 7, 1]]]
 hmul := by decide
 f := ![![![![259200, 45520, -4339], ![-584352, 55980, 0]], ![![5472, -60192, 0], ![0, 0, 0]]], ![![![60128, 10545, -1010], ![-135556, 13023, 0]], ![![1273, -13984, 0], ![0, 0, 0]]]]
 g := ![![![![2614, 39, 0], ![-11232, 0, 0]], ![![1132, 17, 0], ![-4864, 0, 0]]], ![![![132, 2, 0], ![-567, 0, 0]], ![![14, 0, 0], ![-60, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![288, 0, 0], ![67, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl
