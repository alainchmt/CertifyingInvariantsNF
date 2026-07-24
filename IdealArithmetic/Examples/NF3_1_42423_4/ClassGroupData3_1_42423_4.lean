import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_42423_4.RI3_1_42423_4

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![43, 6, 4]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![129, -73, 39]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![5, 1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![5, 1, 1]] ![![3, 0, 0], ![5, 1, 1]]
  ![![3, 0, 0], ![4, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![15, 3, 3]], ![![15, 3, 3], ![77, 12, 5]]]
 hmul := by decide
 f := ![![![![9214743, 14060853, -10404928], ![16576549, 0, -7335360]], ![![0, 0, 0], ![-19099, 0, -56]]], ![![![11847592, 18078344, -13377843], ![21312832, 0, -9431232]], ![![0, 0, 0], ![-24556, 0, -72]]]]
 g := ![![![![-1, 0, -1], ![3, 0, 0]], ![![1, 1, 0], ![3, 0, 0]]], ![![![1, 1, 0], ![3, 0, 0]], ![![7, 4, -3], ![14, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![3, 0, 0], ![4, 0, 1]] ![![3, 0, 0], ![5, 1, 1]]
  ![![43, 6, 4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![9, 0, 0], ![15, 3, 3]], ![![12, 0, 3], ![35, 12, 2]]]
 hmul := by decide
 f := ![![![![8622, 13188, -9740], ![15522, 0, -6864]], ![![0, 0, 0], ![-43, 0, 0]]]]
 g := ![![![![7, -2, 0]], ![![-13, 3, 1]]], ![![![-16, 2, 3]], ![![13, 2, -6]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![289712, 40408, 27297])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![5, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![4, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
