import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_42316_1.RI3_1_42316_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-72218, -4318, -5042]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![152429, 101972, -134938]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![10, 0, 0], ![1, 1, 0]] ![![10, 0, 0], ![1, 1, 0]]
  ![![-72218, -4318, -5042]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![100, 0, 0], ![10, 10, 0]], ![![10, 10, 0], ![2, 2, 2]]]
 hmul := by decide
 f := ![![![![-217012, 85959, 0], ![-13100, 0, 0]], ![![0, 0, 0], ![-909397, 302292, 0]]]]
 g := ![![![![23, -121, 96]], ![![355, -125, -5]]], ![![![355, -125, -5]], ![![4, 29, -26]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![3525020071193, 210765651200, 246104310362])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
