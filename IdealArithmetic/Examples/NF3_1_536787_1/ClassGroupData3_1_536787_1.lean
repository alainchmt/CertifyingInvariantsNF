import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_536787_1.RI3_1_536787_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-5, 1, 0]

def alpha1 := B.equivFun.symm ![148, 8, -7]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![253801, 15288, -12306]

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
 f := ![![![![0, -2, -1], ![0, 0, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![0, 53, 17], ![0, 36, 0]], ![![0, 0, 0], ![-142, 1, 0]]]]
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
 f := ![![![![0, 0, 1], ![0, 0, 0]], ![![0, 0, 0], ![-8, 0, 0]]], ![![![0, -3, 15], ![0, 6, 0]], ![![0, 0, 0], ![-144, -1, 0]]]]
 g := ![![![![4, 1, 0], ![-8, 0, 0]], ![![2, 1, 0], ![-4, 0, 0]]], ![![![-4, -4, -1], ![10, 8, 0]], ![![1, -3, -1], ![-3, 9, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![3, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![-5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![8, 8, 0]], ![![6, 2, 0], ![3, 4, 1]]]
 hmul := by decide
 f := ![![![![-908, 594, 86], ![456, 794, 0]], ![![1904, -3794, 0], ![-136, -1, 0]]]]
 g := ![![![![25, 5, 1]], ![![83, 15, 3]]], ![![![27, 5, 1]], ![![84, 16, 3]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow4 : J0 ^ 4 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![1, 1, 1]] ![![5, 0, 0], ![1, 1, 1]]
  ![![148, 8, -7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![5, 5, 5]], ![![5, 5, 5], ![283, 143, 3]]]
 hmul := by decide
 f := ![![![![4759, 2267, -220], ![1365, 0, 0]], ![![0, 0, 0], ![-444, 0, 0]]]]
 g := ![![![![1192, 229, 44]], ![![7937, 1525, 293]]], ![![![7937, 1525, 293]], ![![52855, 10155, 1951]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![90941859649, 17472596988, 3356998050])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 1]]
  ![![10, 0, 0], ![-4, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![2, 2, 2]], ![![5, 5, 0], ![142, 2, 2]]]
 hmul := by decide
 f := ![![![![5, 5, 0], ![5, 0, 0]], ![![-10, -2, 0], ![0, 0, 0]]], ![![![-3, -3, -1], ![3, 0, 0]], ![![4, 1, 0], ![0, 0, 0]]]]
 g := ![![![![-24, 0, -1], ![8, 2, 0]], ![![-24, 0, -1], ![10, 2, 0]]], ![![![-10, 0, -1], ![9, 1, 0]], ![![-106, 24, 23], ![-230, 2, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-4, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![-1, 1, 0]] ![![5, 0, 0], ![1, 1, 1]]
  ![![20, 0, 0], ![6, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![20, 0, 0], ![4, 4, 4]], ![![-5, 5, 0], ![140, 0, 0]]]
 hmul := by decide
 f := ![![![![15, -5, -12], ![5, 0, 0]], ![![60, 44, 0], ![0, 0, 0]]], ![![![4, -2, -4], ![4, 0, 0]], ![![18, 13, 0], ![0, 0, 0]]]]
 g := ![![![![228706, 7167, -1676], ![68892, -35372, 0]], ![![45644, 1430, -335], ![13764, -7060, 0]]], ![![![-57298, -1796, 419], ![-17241, 8861, 0]], ![![1600948, 50170, -11731], ![482224, -247604, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![6, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![8, 0, 0], ![3, 1, 0]] ![![5, 0, 0], ![1, 1, 1]]
  ![![40, 0, 0], ![-14, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![40, 0, 0], ![8, 8, 8]], ![![15, 5, 0], ![144, 4, 4]]]
 hmul := by decide
 f := ![![![![10, 98, 27], ![30, 0, 0]], ![![-40, -264, 0], ![0, 0, 0]]], ![![![-4, -35, -10], ![-8, 0, 0]], ![![14, 93, 0], ![0, 0, 0]]]]
 g := ![![![![1164990, -119673, 19536], ![-410216, -371224, 0]], ![![232810, -23915, 3904], ![-81968, -74184, 0]]], ![![![436752, -44865, 7324], ![-153789, -139171, 0]], ![![4193842, -430811, 70330], ![-1476820, -1336376, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![40, 0, 0], ![-14, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
