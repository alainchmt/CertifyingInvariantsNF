import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF9_1_7126573229_1.RI9_1_7126573229_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![3, 11, 2, 9, 1, 2, -6, 1, -6]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-2, -7, -1, -7, -1, -2, 5, -1, 5]

def zeta2 := B.equivFun.symm ![0, 0, 1, -1, -1, -1, 2, -1, 2]

def zeta3 := B.equivFun.symm ![2, -1, 5, -3, 3, -2, 1, -1, 0]

def zeta4 := B.equivFun.symm ![-2, -8, -1, -7, -1, -2, 5, -1, 5]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0, 0, 0, 0, 0], ![2, -1, 1, 0, 0, 0, 0, 0, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0, 0, 0, 0, 0, 0, 0], ![2, -1, 1, 0, 0, 0, 0, 0, 0]] ![![3, 0, 0, 0, 0, 0, 0, 0, 0], ![2, -1, 1, 0, 0, 0, 0, 0, 0]]
  ![![3, 11, 2, 9, 1, 2, -6, 1, -6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0, 0, 0, 0, 0, 0, 0], ![6, -3, 3, 0, 0, 0, 0, 0, 0]], ![![6, -3, 3, 0, 0, 0, 0, 0, 0], ![4, -4, 5, -2, 1, 0, 0, 0, 0]]]
 hmul := by decide
 f := ![![![![-13607092, -80237391, -4366327, 25882543, -20411473, 9074445, 18698170, -5582474, 4245409], ![16218961, 132558816, 68929056, -66491528, -35123152, 0, 0, -4159480, 37363]], ![![0, 0, 0, 0, 0, 0, 0, 0, 0], ![-6888, 8990, 25322, 886, 1421, 0, 0, -170, 39]]]]
 g := ![![![![2, -8, 7, -7, 13, 0, -7, 3, -9]], ![![-2, -6, 12, -13, 11, -10, 8, -6, 3]]], ![![![-2, -6, 12, -13, 11, -10, 8, -6, 3]], ![![-4, -9, 7, -15, 2, -10, 14, -7, 11]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![0, 1, -4, 3, -3, 2, -1, 1, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![3, 0, 3, 1, 2, 1, -3, 1, -3])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta3 : IsUnit zeta3 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1, 5, 7, 0, 5, -3, 0, -2, -2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta4 : IsUnit zeta4 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1, 1, -4, 3, -3, 4, -4, 3, -2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0, 0, 0, 0, 0, 0, 0], ![2, -1, 1, 0, 0, 0, 0, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
