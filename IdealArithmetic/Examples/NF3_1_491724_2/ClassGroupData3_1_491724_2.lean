import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_491724_2.RI3_1_491724_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-163, -44, -3]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-3511825, -252176, 34278]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![-1, 1, 0]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![49, 0, 0], ![13, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![-7, 7, 0]], ![![-7, 7, 0], ![1, -2, 1]]]
 hmul := by decide
 f := ![![![![0, 8168, -3582], ![0, -1673, 0]], ![![0, 0, 0], ![186739, -245, 0]]], ![![![0, 2134, -936], ![0, -435, 0]], ![![0, 0, 0], ![48781, -64, 0]]]]
 g := ![![![![287, 22, 0], ![-1078, 0, 0]], ![![-41, -16, -1], ![154, 49, 0]]], ![![![-41, -16, -1], ![154, 49, 0]], ![![-9, -1, 0], ![34, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![13, 1, 0]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![-163, -44, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![-49, 49, 0]], ![![91, 7, 0], ![-13, 12, 1]]]
 hmul := by decide
 f := ![![![![-737460, 2499999, 197776], ![-2811560, -223535, 0]], ![![1175330, -8043649, 0], ![-587665, 771, 0]]]]
 g := ![![![![4439, 314, -43]], ![![-5315, -369, 51]]], ![![![509, 37, -5]], ![![-617, -44, 6]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-35547211729, -9737757208, -673992022])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![13, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
