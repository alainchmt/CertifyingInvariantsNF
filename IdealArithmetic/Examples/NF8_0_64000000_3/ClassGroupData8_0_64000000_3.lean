import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF8_0_64000000_3.RI8_0_64000000_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![2, 5, -6, 5, -5, 3, -3, 5]

def v := B.equivFun.symm ![-1, -5, 5, -5, 5, -3, 5, -10]

def zeta1 := B.equivFun.symm ![1, 2, -2, 2, -3, 2, -4, 8]

def zeta2 := B.equivFun.symm ![0, 1, 0, 0, 0, 0, 0, 0]

def zeta3 := B.equivFun.symm ![1, -1, 0, 0, 0, 0, 2, -5]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0]] ![![5, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0]]
  ![![2, 5, -6, 5, -5, 3, -3, 5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0, 0, 0, 0, 0, 0], ![5, 5, 0, 0, 0, 0, 0, 0]], ![![5, 5, 0, 0, 0, 0, 0, 0], ![1, 2, 1, 0, 0, 0, 0, 0]]]
 hmul := by decide
 f := ![![![![9239344, 28641967, -12913595, -26028033, 12582767, 50298905, 29022376, 26217971], ![-33723604, -59593767, 117983208, 6268816, -74867785, -182391640, -6236558, 0]], ![![0, 0, 0, 0, 0, 0, 0, 0], ![58024, 116321, -610148, -665805, -845965, -28252, -138, 0]]]]
 g := ![![![![0, -35, 45, -35, 40, -25, 25, -40]], ![![2, 1, 5, -3, 4, -2, -3, 9]]], ![![![2, 1, 5, -3, 4, -2, -3, 9]], ![![1, 3, 0, 1, -1, 1, -4, 9]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![2, 2, -2, 2, -3, 2, -4, 8])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-4, -10, 11, -10, 11, -7, 11, -21])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta3 : IsUnit zeta3 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1, 1, 0, 0, -1, 1, -2, 4])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 4 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0, 0, 0, 0, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
