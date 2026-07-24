import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_393835_1.RI3_1_393835_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-181, -69, -7]

def alpha1 := B.equivFun.symm ![-439, -68, 10]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![16373785189, -399303314, -102349535]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-51, -5, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-51, -5, 1]] ![![2, 0, 0], ![-51, -5, 1]]
  ![![-181, -69, -7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-102, -10, 2]], ![![-102, -10, 2], ![81, 61, -5]]]
 hmul := by decide
 f := ![![![![242, -2390, 147], ![155, 0, 0]], ![![0, 0, 0], ![181, 0, 0]]]]
 g := ![![![![116, 11, -2]], ![![-298, -81, 10]]], ![![![-298, -81, 10]], ![![-9341, -690, 143]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-52, -5, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![-52, -5, 1]] ![![3, 0, 0], ![-52, -5, 1]]
  ![![-439, -68, 10]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-156, -15, 3]], ![![-156, -15, 3], ![184, 71, -7]]]
 hmul := by decide
 f := ![![![![461, -5159, 329], ![1065, 0, 0]], ![![0, 0, 0], ![878, 0, 0]]]]
 g := ![![![![-671, -256, -26]], ![![-2556, -975, -99]]], ![![![-2556, -975, -99]], ![![-9736, -3713, -377]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![26527032109195423189, 10119424304221131985, 1027651332875264476])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-52, -5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-51, -5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![-51, -5, 1]] ![![3, 0, 0], ![-52, -5, 1]]
  ![![6, 0, 0], ![-49, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![6, 0, 0], ![-104, -10, 2]], ![![-153, -15, 3], ![132, 66, -6]]]
 hmul := by decide
 f := ![![![![50, 5, -1], ![-6, 0, 0]], ![![6, 0, 0], ![0, 0, 0]]], ![![![25, 0, 0], ![74, 0, 0]], ![![-49, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![48, 5, -1], ![8, 0, 0]]], ![![![48, 5, -1], ![9, 0, 0]], ![![22, 11, -1], ![0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![-49, -5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
