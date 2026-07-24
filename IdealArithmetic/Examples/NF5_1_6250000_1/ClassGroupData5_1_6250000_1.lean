import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_6250000_1.RI5_1_6250000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![0, 1, -1, -1, -4]

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-11, 18, -2, 2, -3]

def zeta2 := B.equivFun.symm ![5, 3, 5, 2, 8]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![4, 0, -4, -2, -6]], ![![4, 0, -4, -2, -6], ![10, 7, -3, -1, -6]]]
 hmul := by decide
 f := ![![![![-66232, 10472, -17929, -13613, -36906], ![13872, -31416, -5749, 3412, 0]], ![![0, 0, 0, 0, 0], ![-1425, -175, 21, -1, 0]]], ![![![-209684, 33154, -56766, -43101, -116851], ![43914, -99462, -18202, 10803, 0]], ![![0, 0, 0, 0, 0], ![-4512, -554, 66, -3, 0]]]]
 g := ![![![![36, -30, 8, -3, 20], ![-2, 16, -4, 0, 0]], ![![32, -32, 8, -3, 21], ![0, 16, -4, 0, 0]]], ![![![32, -32, 8, -3, 21], ![0, 16, -4, 0, 0]], ![![32, -34, 9, -4, 21], ![3, 19, -3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![4, 0, 0, 0, 0], ![2, 11, -9, -3, -14]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![4, 0, -4, -2, -6]], ![![8, 4, -4, -2, -8], ![8, 8, -12, -5, -20]]]
 hmul := by decide
 f := ![![![![114, -28, 147, -63, -13], ![26, 84, -60, 116, 0]], ![![0, 0, 0, 0, 0], ![-20, 16, -4, 0, 0]]], ![![![625, -106, -1028, -344, -1281], ![-877, -73, 13, -156, 0]], ![![0, 0, 0, 0, 0], ![31, -25, 9, 0, 0]]]]
 g := ![![![![914, -63, -94, 31, 86], ![208, 464, 36, 0, 0]], ![![2217, -149, -233, 75, 205], ![503, 1125, 87, -1, 0]]], ![![![4604, -308, -484, 156, 424], ![1044, 2336, 180, -2, 0]], ![![8608, -561, -919, 289, 776], ![1946, 4366, 336, -5, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![2, 11, -9, -3, -14]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![8, 0, -8, -4, -12]], ![![4, 22, -18, -6, -28], ![-2, 39, -25, -7, -40]]]
 hmul := by decide
 f := ![![![![4002981397320, -879281682960, 1301355522905, 710156487738, 2083664126898], ![-778948559800, 2051657260240, 100798938720, -36943461676, 0]], ![![6390871272, -624010836, 69187404, 0, 0], ![-990795, 49945, -1817, -49, 0]]], ![![![5150620277056, -1131368251806, 1674448986554, 913755534331, 2681042362515], ![-1002270020434, 2639859254214, 129697594404, -47535005518, 0]], ![![8223108702, -802912266, 89023158, 0, 0], ![-1274852, 64264, -2338, -63, 0]]]]
 g := ![![![![-484, 834, 24, 303, 108], ![-252, -1104, -120, 0, 0]], ![![-452, 780, 20, 282, 97], ![-236, -1032, -112, 0, 0]]], ![![![1086, -1906, -58, -695, -255], ![598, 2526, 282, 0, 0]], ![![2445, -4278, -126, -1557, -564], ![1333, 5667, 629, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![0, 1, -1, -1, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![8, 0, -8, -4, -12]], ![![8, 4, -4, -2, -8], ![8, 8, -12, -5, -20]]]
 hmul := by decide
 f := ![![![![-606792, 133416, -197518, -106843, -315632], ![117600, -311304, -15085, 4897, 0]], ![![-2429, -2445, 105, 0, 0], ![119, -3, 1, 0, 0]]]]
 g := ![![![![-8, -17, -13, -8, -17]], ![![37, 17, 31, 15, 40]]], ![![![0, -10, -10, -6, -14]], ![![30, 14, 14, 7, 16]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow5 : J0 ^ 5 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1, 2, 0, -6, -9])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![27, -105, 67, 16, 104])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![2, 11, -9, -3, -14]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
