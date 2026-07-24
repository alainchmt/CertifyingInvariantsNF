import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_623807_1.RI3_1_623807_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-23, -4, -1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![18053076206431487, -82494427526000, -894686488587598]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 0, 1]] ![![2, 0, 0], ![1, 0, 1]]
  ![![4, 0, 0], ![-1, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 0, 2]], ![![2, 0, 2], ![-151, 76, 3]]]
 hmul := by decide
 f := ![![![![9766, 0, -2017], ![3876, -152, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![-2442, 0, 504], ![-968, 38, 0]], ![![0, 0, 0], ![-1, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 1], ![-2, 0, 0]]], ![![![0, 0, 1], ![-2, 0, 0]], ![![2691, 0, 141], ![-637, -76, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![-1, 0, 1]] ![![2, 0, 0], ![1, 0, 1]]
  ![![8, 0, 0], ![3, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 0, 4]], ![![-2, 0, 2], ![-153, 76, 1]]]
 hmul := by decide
 f := ![![![![1887, 0, -9436], ![-3774, 0, 0]], ![![45592, 304, 0], ![8, 0, 0]]], ![![![707, 0, -3539], ![-1414, 0, 0]], ![![17097, 114, 0], ![3, 0, 0]]]]
 g := ![![![![-2, 0, -1], ![8, 0, 0]], ![![-1, 0, 0], ![4, 0, 0]]], ![![![-1, 0, 0], ![2, 0, 0]], ![![-3825, -76, 204], ![-1403, 228, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![3, 0, 1]] ![![2, 0, 0], ![1, 0, 1]]
  ![![16, 0, 0], ![3, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![8, 0, 8]], ![![6, 0, 2], ![-149, 76, 5]]]
 hmul := by decide
 f := ![![![![-1448415, 0, -163210], ![-805810, 3040, 0]], ![![4536784, -4256, 0], ![16, 0, 0]]], ![![![-271578, 0, -30602], ![-151089, 570, 0]], ![![850647, -798, 0], ![3, 0, 0]]]]
 g := ![![![![-2, 0, -1], ![16, 0, 0]], ![![-1, 0, 0], ![8, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-7683, -152, 142], ![-1431, 836, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![3, 0, 1]] ![![2, 0, 0], ![1, 0, 1]]
  ![![-23, -4, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![16, 0, 16]], ![![6, 0, 2], ![-149, 76, 5]]]
 hmul := by decide
 f := ![![![![-27538446, 0, -2349826], ![-14944135, 114794, 0]], ![![157717017, -344382, 0], ![3017, -4, 0]]]]
 g := ![![![![-8, 4, -1]], ![![376, -36, -7]]], ![![![46, -4, -1]], ![![-205, -40, 24]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow5 : J0 ^ 5 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![359445365099381575938346834514847, 62257534245066044355139039743904, 16017840721099624463728891802226])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-1, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![3, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![3, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
