import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_439052_1.RI3_1_439052_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![68, -19, 3]

def alpha1 := B.equivFun.symm ![66, -6, -2]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![4500, -501, -148]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-39, 2, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-39, 2, 1]] ![![5, 0, 0], ![-39, 2, 1]]
  ![![68, -19, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-195, 10, 5]], ![![-195, 10, 5], ![328, -49, -12]]]
 hmul := by decide
 f := ![![![![35, -265, -30], ![-339, 0, 0]], ![![0, 0, 0], ![-204, 0, 0]]]]
 g := ![![![![47, -2, -1]], ![![-128, 13, 4]]], ![![![-128, 13, 4]], ![![-226, -13, 1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![38, 0, 0], ![3, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![38, 0, 0], ![3, 1, 0]] ![![38, 0, 0], ![3, 1, 0]]
  ![![66, -6, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![1444, 0, 0], ![114, 38, 0]], ![![114, 38, 0], ![10, 6, 2]]]
 hmul := by decide
 f := ![![![![-36497, -114771, -76768], ![-5888, 1462312, 0]], ![![0, 0, 0], ![-150356, 1285, 0]]]]
 g := ![![![![-133, 19, 0]], ![![-10, -2, 1]]], ![![![-10, -2, 1]], ![![-8, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1383256, -384037, 59334])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![38, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-39, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![-39, 2, 1]] ![![38, 0, 0], ![3, 1, 0]]
  ![![190, 0, 0], ![-133, 9, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![190, 0, 0], ![15, 5, 0]], ![![-1482, 76, 38], ![-387, 21, 8]]]
 hmul := by decide
 f := ![![![![-73490, -232021, -154864], ![-11894, 2940972, 0]], ![![380, 0, 0], ![0, 0, 0]]], ![![![51440, 162414, 108405], ![8365, -2058684, 0]], ![![-266, 0, 0], ![0, 0, 0]]]]
 g := ![![![![2280, 213, -106], ![-1330, 1140, 0]], ![![222, 14, -9], ![-45, 90, 0]]], ![![![-16720, -1733, 811], ![11894, -8892, 0]], ![![-4315, -456, 211], ![3179, -2322, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![190, 0, 0], ![-133, 9, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
