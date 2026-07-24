import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_441484_2.RI3_1_441484_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![96, -5, 8]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![252880219, -2373222, -17975042]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![9, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![3, 5, 11]]]
 hmul := by decide
 f := ![![![![-10329, -16903, -41316], ![-5633, 10329, 0]], ![![0, 0, 0], ![2811, 6, 0]]], ![![![3443, 5634, 13772], ![1879, -3443, 0]], ![![0, 0, 0], ![-937, -2, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![3, 0, 0]]], ![![![1, 0, 0], ![3, 0, 0]], ![![16, 10, 55], ![3, -44, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-3, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![96, -5, 8]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![0, 9, 0]], ![![-9, 3, 0], ![3, 2, 11]]]
 hmul := by decide
 f := ![![![![-158668, -250620, -634672], ![-83539, 158668, 0]], ![![39667, 39667, 0], ![10865, 23, 0]]]]
 g := ![![![![34, -4, -5]], ![![211, 8, -8]]], ![![![59, 4, -1]], ![![47, 27, 16]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-58417367385518789, 3059430149554622, -4869761950443934])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
