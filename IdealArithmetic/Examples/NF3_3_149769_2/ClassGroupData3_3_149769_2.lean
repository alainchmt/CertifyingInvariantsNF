import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_149769_2.RI3_3_149769_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![271, 18, -3]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![6, 1, 0]

def zeta2 := B.equivFun.symm ![92, 6, -1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-5, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![13, 0, 0], ![-5, 1, 0]] ![![13, 0, 0], ![-5, 1, 0]]
  ![![169, 0, 0], ![-57, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![169, 0, 0], ![-65, 13, 0]], ![![-65, 13, 0], ![25, -10, 1]]]
 hmul := by decide
 f := ![![![![912799186, -201004679, 3691558], ![2371010512, -47562021, 0]], ![![0, 0, 0], ![-5668429, -10140, 0]]], ![![![-308407274, 67913415, -1247267], ![-801092836, 16069784, 0]], ![![0, 0, 0], ![1915191, 3426, 0]]]]
 g := ![![![![6385, -112, 0], ![18928, 0, 0]], ![![-2447, 100, -1], ![-7254, 169, 0]]], ![![![-2447, 100, -1], ![-7254, 169, 0]], ![![985, -17, 0], ![2920, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![169, 0, 0], ![-57, 1, 0]] ![![13, 0, 0], ![-5, 1, 0]]
  ![![271, 18, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![2197, 0, 0], ![-845, 169, 0]], ![![-741, 13, 0], ![285, -62, 1]]]
 hmul := by decide
 f := ![![![![5614426937862, -1218816607618, 18879771778], ![14596636008106, -245038614676, 0]], ![![993216290, -5178822170, 0], ![-9029239, -16152, 0]]]]
 g := ![![![![1846, 153, -24]], ![![-1742, -155, 21]]], ![![![-702, -59, 9]], ![![657, 58, -8]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-93, -6, 1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![79, 7, -1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![-57, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
