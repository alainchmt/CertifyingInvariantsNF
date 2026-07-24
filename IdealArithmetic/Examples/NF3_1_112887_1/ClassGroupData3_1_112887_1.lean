import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_112887_1.RI3_1_112887_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![2, 1, -1]

def alpha1 := B.equivFun.symm ![23, 2, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![15, -3, -2]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![15, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![15, 0, 0], ![1, 1, 0]] ![![15, 0, 0], ![1, 1, 0]]
  ![![2, 1, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![225, 0, 0], ![15, 15, 0]], ![![15, 15, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -7, -3], ![0, 4, 0]], ![![0, 0, 0], ![638, -12, 0]]]]
 g := ![![![![-603, -51, -24]], ![![-125, -10, -5]]], ![![![-125, -10, -5]], ![![-26, -2, -1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![3, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![13, 0, 0], ![3, 1, 0]] ![![13, 0, 0], ![3, 1, 0]]
  ![![23, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![169, 0, 0], ![39, 13, 0]], ![![39, 13, 0], ![9, 6, 1]]]
 hmul := by decide
 f := ![![![![-991330, -354320, -7927], ![4283770, 99056, 0]], ![![0, 0, 0], ![53970, -339, 0]]]]
 g := ![![![![-18, 7, 2]], ![![4, -3, 1]]], ![![![4, -3, 1]], ![![5, -2, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![3120, 257, 123])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![15, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![15, 0, 0], ![1, 1, 0]] ![![13, 0, 0], ![3, 1, 0]]
  ![![195, 0, 0], ![16, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![195, 0, 0], ![45, 15, 0]], ![![13, 13, 0], ![3, 4, 1]]]
 hmul := by decide
 f := ![![![![-36096, -12869, -198], ![156026, 3757, 0]], ![![1365, -1365, 0], ![0, 0, 0]]], ![![![-2976, -1062, -17], ![12864, 312, 0]], ![![112, -105, 0], ![0, 0, 0]]]]
 g := ![![![![913, 57, 0], ![-11115, 0, 0]], ![![191, 12, 0], ![-2325, 0, 0]]], ![![![31, 2, 0], ![-377, 0, 0]], ![![-15, -1, 0], ![183, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![195, 0, 0], ![16, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
