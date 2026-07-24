import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_181804_1.RI3_1_181804_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-81, -16, -4]

def alpha1 := B.equivFun.symm ![3, 1, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![9, 22, -6]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![9, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -291, -116], ![0, -135, 0]], ![![0, 0, 0], ![1485, -18, 0]]], ![![![0, -114, -46], ![0, -50, 0]], ![![0, 0, 0], ![578, -7, 0]]]]
 g := ![![![![5, 1, 0], ![-9, 0, 0]], ![![-1, 0, 0], ![3, 0, 0]]], ![![![-1, 0, 0], ![3, 0, 0]], ![![-3, -1, 0], ![7, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![4, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![27, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![12, 3, 0], ![4, 5, 1]]]
 hmul := by decide
 f := ![![![![40095, 40095, 31855], ![26730, -90585, 0]], ![![-106920, -11880, 0], ![-8910, -54, 0]]], ![![![5202, 5202, 4132], ![3468, -11749, 0]], ![![-13872, -1544, 0], ![-1156, -7, 0]]]]
 g := ![![![![21, 5, 0], ![-135, 0, 0]], ![![7, 2, 0], ![-45, 0, 0]]], ![![![4, 1, 0], ![-24, 0, 0]], ![![4, 1, 0], ![-26, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![27, 0, 0], ![4, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![-81, -16, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0, 0], ![27, 27, 0]], ![![12, 3, 0], ![4, 5, 1]]]
 hmul := by decide
 f := ![![![![216954, -573481, -98676], ![-253113, -296367, 0]], ![![-903975, 5323275, 0], ![24106, 146, 0]]]]
 g := ![![![![-1, -16, 4]], ![![109, -11, -4]]], ![![![12, -3, 0]], ![![4, 3, -1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow4 : J0 ^ 4 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![3, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![3, 1, 0]] ![![11, 0, 0], ![3, 1, 0]]
  ![![3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![33, 11, 0]], ![![33, 11, 0], ![9, 6, 1]]]
 hmul := by decide
 f := ![![![![-37760, -14551, -642], ![125876, 2837, 0]], ![![0, 0, 0], ![47165, -115, 0]]]]
 g := ![![![![13, -3, 1]], ![![11, 0, 0]]], ![![![11, 0, 0]], ![![3, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![13849, 2754, 682])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![1, 1, 0]] ![![11, 0, 0], ![3, 1, 0]]
  ![![33, 0, 0], ![-8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![33, 0, 0], ![9, 3, 0]], ![![11, 11, 0], ![3, 4, 1]]]
 hmul := by decide
 f := ![![![![126, 41, -10], ![-418, -11, 0]], ![![-33, 33, 0], ![0, 0, 0]]], ![![![-34, -13, 2], ![114, 11, 0]], ![![8, -9, 0], ![0, 0, 0]]]]
 g := ![![![![249, -31, 0], ![1023, 0, 0]], ![![81, -10, 0], ![333, 0, 0]]], ![![![83, -10, 0], ![341, 0, 0]], ![![27, -3, 0], ![111, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![33, 0, 0], ![-8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![9, 0, 0], ![4, 1, 0]] ![![11, 0, 0], ![3, 1, 0]]
  ![![99, 0, 0], ![-41, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![99, 0, 0], ![27, 9, 0]], ![![44, 11, 0], ![12, 7, 1]]]
 hmul := by decide
 f := ![![![![327, -170, -66], ![-1034, -121, 0]], ![![-99, 693, 0], ![0, 0, 0]]], ![![![-137, 69, 27], ![434, 55, 0]], ![![41, -288, 0], ![0, 0, 0]]]]
 g := ![![![![1846, -45, 0], ![4455, 0, 0]], ![![496, -12, 0], ![1197, 0, 0]]], ![![![866, -21, 0], ![2090, 0, 0]], ![![266, -6, 0], ![642, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![99, 0, 0], ![-41, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![27, 0, 0], ![4, 1, 0]] ![![11, 0, 0], ![3, 1, 0]]
  ![![297, 0, 0], ![58, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![297, 0, 0], ![81, 27, 0]], ![![44, 11, 0], ![12, 7, 1]]]
 hmul := by decide
 f := ![![![![6081, -3244, -1246], ![-19228, -2387, 0]], ![![-5643, 39501, 0], ![0, 0, 0]]], ![![![1184, -633, -243], ![-3742, -462, 0]], ![![-1102, 7695, 0], ![0, 0, 0]]]]
 g := ![![![![7599, 131, 0], ![-38907, 0, 0]], ![![2083, 36, 0], ![-10665, 0, 0]]], ![![![1100, 19, 0], ![-5632, 0, 0]], ![![300, 5, 0], ![-1536, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![297, 0, 0], ![58, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
