import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_806284_1.RI3_3_806284_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-11, 1, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![56, 20, -5]

def zeta2 := B.equivFun.symm ![2941, 1016, -254]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-34, -1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-34, -1, 1]] ![![2, 0, 0], ![-34, -1, 1]]
  ![![2, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-68, -2, 2]], ![![-68, -2, 2], ![847, -7, -12]]]
 hmul := by decide
 f := ![![![![-52895, 30573529, 82959], ![-14345535, -4719120, 0]], ![![0, 0, 0], ![-3710, 3, 0]]], ![![![-52893, 30565288, 82937], ![-14341669, -4717848, 0]], ![![0, 0, 0], ![-3709, 3, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-29, 4, 1], ![-10, 0, 0]]], ![![![-29, 4, 1], ![-10, 0, 0]], ![![353, -74, -6], ![141, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![-34, -1, 1]]
  ![![-11, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0], ![-68, -2, 2]], ![![2, 2, 0], ![69, 15, -2]]]
 hmul := by decide
 f := ![![![![29, -7525, -18], ![3512, 1155, 0]], ![![0, 0, 0], ![11, 0, 0]]]]
 g := ![![![![9, 6, 1]], ![![53, 31, 5]]], ![![![56, 36, 6]], ![![284, 185, 31]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![46, 30, 5])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1841481, 20320, -37338])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-34, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
