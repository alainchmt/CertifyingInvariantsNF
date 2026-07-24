import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_213716_1.RI3_1_213716_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-3, 1, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-15, 10, 4]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -2, -1], ![0, 0, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![0, -31, -12], ![0, -21, 0]], ![![0, 0, 0], ![87, 1, 0]]]]
 g := ![![![![0, -1, 0], ![4, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![8, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![2, 2, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -4, -3], ![0, 4, 0]], ![![0, 0, 0], ![8, 0, 0]]], ![![![0, -8, 1], ![0, -16, 0]], ![![0, -15, 0], ![83, 1, 0]]]]
 g := ![![![![16, -5, 0], ![40, 0, 0]], ![![8, -2, 0], ![20, 0, 0]]], ![![![4, -1, 0], ![10, 0, 0]], ![![-1, 4, -1], ![-3, 9, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![-3, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![16, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![8, 8, 0]], ![![-6, 2, 0], ![-3, -2, 1]]]
 hmul := by decide
 f := ![![![![-108, 21, -38], ![56, 46, 0]], ![![-224, 112, 0], ![16, 0, 0]]], ![![![-554, 102, -190], ![278, 235, 0]], ![![-1162, 539, 0], ![83, 1, 0]]]]
 g := ![![![![40, -13, 0], ![208, 0, 0]], ![![20, -6, 0], ![104, 0, 0]]], ![![![-12, 7, -1], ![-62, 16, 0]], ![![-6, 2, 0], ![-31, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![-3, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![32, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![16, 16, 0]], ![![-6, 2, 0], ![-3, -2, 1]]]
 hmul := by decide
 f := ![![![![-44, 138, -81], ![24, 52, 0]], ![![-192, 864, 0], ![32, 0, 0]]], ![![![-112, 358, -208], ![58, 133, 0]], ![![-498, 2223, 0], ![83, 1, 0]]]]
 g := ![![![![40, -13, 0], ![416, 0, 0]], ![![20, -6, 0], ![208, 0, 0]]], ![![![-6, 5, -1], ![-62, 32, 0]], ![![-3, 1, 0], ![-31, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![-3, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![64, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![32, 32, 0]], ![![-6, 2, 0], ![-3, -2, 1]]]
 hmul := by decide
 f := ![![![![-428, 1226, -721], ![216, 468, 0]], ![![-3456, 15552, 0], ![64, 0, 0]]], ![![![-554, 1578, -928], ![278, 603, 0]], ![![-4482, 20007, 0], ![83, 1, 0]]]]
 g := ![![![![136, -45, 0], ![2880, 0, 0]], ![![68, -22, 0], ![1440, 0, 0]]], ![![![-12, 7, -1], ![-254, 64, 0]], ![![-6, 2, 0], ![-127, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![64, 0, 0], ![-3, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![128, 0, 0], ![64, 64, 0]], ![![-6, 2, 0], ![-3, -2, 1]]]
 hmul := by decide
 f := ![![![![-280, 6324, 9869], ![7810, -19901, 81]], ![![2974, -9, 0], ![83, 1, 0]]]]
 g := ![![![![-14, -2, -1]], ![![36, -4, -2]]], ![![![2, 0, 0]], ![![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow7 : J0 ^ 7 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-7935, 1494, -328])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     

lemma PowJ0_6 : J0 ^ 6 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
