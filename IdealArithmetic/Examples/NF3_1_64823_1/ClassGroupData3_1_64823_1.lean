import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_64823_1.RI3_1_64823_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-15, -4, -1]

def alpha1 := B.equivFun.symm ![-1, -1, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-15, 4, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![11, 0, 0], ![2, 1, 0]] ![![11, 0, 0], ![2, 1, 0]]
  ![![-15, -4, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![22, 11, 0]], ![![22, 11, 0], ![4, 4, 1]]]
 hmul := by decide
 f := ![![![![310411, 161874, 3294], ![-1698580, -31628, 0]], ![![0, 0, 0], ![-52083, 354, 0]]]]
 g := ![![![![-44, 11, 0]], ![![-8, -2, 1]]], ![![![-8, -2, 1]], ![![3, -1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![7, 0, 0], ![1, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![-1, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![7, 7, 0]], ![![7, 7, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, 7, 3], ![0, 6, 0]], ![![0, 0, 0], ![-197, 4, 0]]]]
 g := ![![![![0, 1, -1]], ![![-7, 0, 0]]], ![![![-7, 0, 0]], ![![-1, -1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![209, 60, 16])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![11, 0, 0], ![2, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![77, 0, 0], ![-20, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![77, 0, 0], ![11, 11, 0]], ![![14, 7, 0], ![2, 3, 1]]]
 hmul := by decide
 f := ![![![![190, -430, -276], ![-637, -126, 0]], ![![-539, 3234, 0], ![0, 0, 0]]], ![![![-50, 112, 72], ![170, 35, 0]], ![![140, -847, 0], ![0, 0, 0]]]]
 g := ![![![![741, -37, 0], ![2849, 0, 0]], ![![123, -6, 0], ![473, 0, 0]]], ![![![142, -7, 0], ![546, 0, 0]], ![![26, -1, 0], ![100, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![77, 0, 0], ![-20, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
