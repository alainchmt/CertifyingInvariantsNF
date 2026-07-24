import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_600925_1.RI3_3_600925_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-13, -3, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-39, -13, -2]

def zeta2 := B.equivFun.symm ![-75624369, -18172361, 4821200]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-30, -2, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-30, -2, 1]] ![![3, 0, 0], ![-30, -2, 1]]
  ![![9, 0, 0], ![-27, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-90, -6, 3]], ![![-90, -6, 3], ![462, 8, -7]]]
 hmul := by decide
 f := ![![![![-49419, -526308, -48542], ![828945, 170181, 0]], ![![0, 0, 0], ![1125, 9, 0]]], ![![![148205, 1577974, 145537], ![-2485331, -510235, 0]], ![![0, 0, 0], ![-3373, -27, 0]]]]
 g := ![![![![72, 50, 3], ![-171, -36, 0]], ![![-549, -488, -36], ![1767, 360, 0]]], ![![![-549, -488, -36], ![1767, 360, 0]], ![![2865, 2506, 184], ![-9055, -1848, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-27, -2, 1]] ![![3, 0, 0], ![-30, -2, 1]]
  ![![-13, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![-270, -18, 9]], ![![-81, -6, 3], ![372, 2, -4]]]
 hmul := by decide
 f := ![![![![261189559, 2810062222, 251126724], ![-4401561229, -903608201, 0]], ![![103605288, 588559, 0], ![4726, -13, 0]]]]
 g := ![![![![683, 29, -16]], ![![-4640, -197, 109]]], ![![![-1319, -56, 31]], ![![8956, 380, -210]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-13593, -577, 319])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![36928533, 13587451, 3473837])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-30, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-27, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
