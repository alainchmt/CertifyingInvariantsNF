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
  ![![4, 0, 0, 0, 0], ![4, 2, -6, -3, -10]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0, 0], ![4, 0, -4, -2, -6]], ![![8, 4, -4, -2, -8], ![8, 8, -12, -5, -20]]]
 hmul := by decide
 f := ![![![![114, -28, 147, -63, -13], ![26, 84, -60, 116, 0]], ![![0, 0, 0, 0, 0], ![-20, 16, -4, 0, 0]]], ![![![-919, 142, -206, -227, -538], ![209, -426, -94, 98, 0]], ![![0, 0, 0, 0, 0], ![-15, 10, -2, 0, 0]]]]
 g := ![![![![-1172, -96, -307, -20, -336], ![108, -456, -52, 0, 0]], ![![6200, 500, 1637, 115, 1799], ![-565, 2415, 273, 3, 0]]], ![![![13514, 1090, 3560, 247, 3910], ![-1236, 5262, 594, 6, 0]], ![![36697, 2964, 9667, 669, 10616], ![-3356, 14289, 1615, 15, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0, 0], ![4, 2, -6, -3, -10]] ![![2, 0, 0, 0, 0], ![2, 0, -2, -1, -3]]
  ![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0, 0], ![8, 0, -8, -4, -12]], ![![8, 4, -12, -6, -20], ![20, 22, -10, -3, -20]]]
 hmul := by decide
 f := ![![![![6379941069, -1401024177, 2063329409, 1141886573, 3325680533], ![-1242852420, 3269056413, 157589967, -72233891, 0]], ![![16647177, 5899824, -57909, 0, 0], ![-204337, 19393, -543, -49, 0]]], ![![![8168740440, -1793841468, 2641842972, 1462047214, 4258130390], ![-1591321724, 4185630092, 201774808, -92486757, 0]], ![![21314697, 7554027, -74112, 0, 0], ![-261620, 24829, -695, -63, 0]]]]
 g := ![![![![-484, 834, 24, 303, 108], ![-252, -1104, -120, 0, 0]], ![![-452, 780, 20, 282, 97], ![-236, -1032, -112, 0, 0]]], ![![![-206, 344, 8, 124, 41], ![-98, -456, -48, 0, 0]], ![![101, -194, -10, -75, -38], ![75, 264, 36, 0, 0]]]]
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

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![4, 2, -6, -3, -10]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0, 0], ![4, 2, -2, -1, -4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
