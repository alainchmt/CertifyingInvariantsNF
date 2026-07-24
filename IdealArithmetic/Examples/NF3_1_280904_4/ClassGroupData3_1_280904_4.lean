import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_280904_4.RI3_1_280904_4

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![41, -6, 2]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![41678521, 5982362, -1142786]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![2, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![49, 0, 0], ![16, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![14, 7, 0], ![5, 4, 2]]]
 hmul := by decide
 f := ![![![![4987838, 11326610, 11778532], ![3043187, -41286518, 0]], ![![0, 0, 0], ![427917, 735, 0]]], ![![![1608330, 3652271, 3797994], ![981281, -13312860, 0]], ![![0, 0, 0], ![137982, 237, 0]]]]
 g := ![![![![-683, -13239, -1656], ![-441, 40572, 0]], ![![-204, -3742, -468], ![-91, 11466, 0]]], ![![![-204, -3742, -468], ![-91, 11466, 0]], ![![-79, -1328, -166], ![-12, 4068, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![16, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![41, -6, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![98, 49, 0]], ![![112, 7, 0], ![33, 18, 2]]]
 hmul := by decide
 f := ![![![![357777908267, 809476596863, 840719118040], ![217861773343, -2942566136560, 0]], ![![1027385145, 344627354, 0], ![-455924, 633, 0]]]]
 g := ![![![![-73, -2, 6]], ![![-106, -17, 2]]], ![![![-36, -3, 2]], ![![-39, -8, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-2562823701140543, 354340526960834, -121512099849634])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![16, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
