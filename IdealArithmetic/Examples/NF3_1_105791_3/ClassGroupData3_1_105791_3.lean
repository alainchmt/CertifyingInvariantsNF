import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_105791_3.RI3_1_105791_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-4, 1, 0]

def alpha1 := B.equivFun.symm ![-5, 1, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![2, -5, 1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![9, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![1, -2, 1]]]
 hmul := by decide
 f := ![![![![0, 234, -95], ![0, -108, 0]], ![![0, 0, 0], ![1143, -18, 0]]], ![![![0, -129, 52], ![0, 62, 0]], ![![0, 0, 0], ![-634, 10, 0]]]]
 g := ![![![![37, -9, 0], ![81, 0, 0]], ![![-7, 6, -1], ![-15, 9, 0]]], ![![![-7, 6, -1], ![-15, 9, 0]], ![![5, -1, 0], ![11, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-4, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 9, 0]], ![![-12, 3, 0], ![4, -5, 1]]]
 hmul := by decide
 f := ![![![![-15216, 29153, -3352], ![-24726, -5762, 0]], ![![-15216, 47048, 0], ![1268, 10, 0]]]]
 g := ![![![![9, 4, 1]], ![![18, 4, 1]]], ![![![3, 0, 0]], ![![-1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![9, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -409, -180], ![0, -195, 0]], ![![0, 0, 0], ![2277, -36, 0]]], ![![![0, -159, -70], ![0, -76, 0]], ![![0, 0, 0], ![886, -14, 0]]]]
 g := ![![![![5, 1, 0], ![-9, 0, 0]], ![![-1, 0, 0], ![3, 0, 0]]], ![![![-1, 0, 0], ![3, 0, 0]], ![![-3, -1, 0], ![7, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![9, 0, 0], ![4, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![-5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![12, 3, 0], ![4, 5, 1]]]
 hmul := by decide
 f := ![![![![-12519, -12519, -9724], ![-8346, 27400, 0]], ![![33384, 4352, 0], ![2782, 22, 0]]]]
 g := ![![![![-18, -5, -1]], ![![-27, -10, -2]]], ![![![-15, -5, -1]], ![![-26, -9, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![221, 73, 16])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0], ![-4, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![-3, 3, 0], ![-1, 0, 1]]]
 hmul := by decide
 f := ![![![![0, -1, 0], ![1, 1, 0]], ![![1, 0, 0], ![-3, 0, 0]]], ![![![0, 0, -1], ![-1, 2, 0]], ![![-1, 0, 0], ![4, 0, 0]]]]
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![1, 1, 0], ![0, 0, 0]]], ![![![3, 1, -1], ![3, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-4, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![-1, 1, 0]] ![![9, 0, 0], ![4, 1, 0]]
  ![![9, 0, 0], ![4, -3, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![27, 0, 0], ![12, 3, 0]], ![![-9, 9, 0], ![-4, 3, 1]]]
 hmul := by decide
 f := ![![![![1645, 549, 48], ![-3597, -438, 0]], ![![130, 0, 0], ![18, 0, 0]]], ![![![44, 15, 1], ![-96, -12, 0]], ![![0, 0, 0], ![8, 0, 0]]]]
 g := ![![![![325, 60, 32], ![126, 54, 0]], ![![137, 27, 14], ![57, 23, 0]]], ![![![-128, -21, -12], ![-45, -21, 0]], ![![-55, -9, -5], ![-19, -9, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![4, -3, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![9, 0, 0], ![-4, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![9, 0, 0], ![22, 6, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![-12, 3, 0], ![-4, -3, 1]]]
 hmul := by decide
 f := ![![![![2998, 799, 248], ![-3497, -650, 0]], ![![4116, -288, 0], ![18, 0, 0]]], ![![![8904, 2441, 713], ![-10386, -1915, 0]], ![![12228, -688, 0], ![44, 0, 0]]]]
 g := ![![![![2485, -2334, 1460], ![3933, 432, 0]], ![![677, -651, 408], ![1098, 120, 0]]], ![![![-1172, 1075, -672], ![-1812, -200, 0]], ![![-334, 299, -187], ![-505, -56, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![22, 6, -4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![9, 0, 0], ![-4, 1, 0]] ![![9, 0, 0], ![4, 1, 0]]
  ![![9, 0, 0], ![-7, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![81, 0, 0], ![36, 9, 0]], ![![-36, 9, 0], ![-16, 0, 1]]]
 hmul := by decide
 f := ![![![![48477, 16765, 1207], ![-108233, -10868, 0]], ![![820, 0, 0], ![45, 0, 0]]], ![![![-37723, -13049, -940], ![84223, 8464, 0]], ![![-638, 0, 0], ![-35, 0, 0]]]]
 g := ![![![![9, 0, 0], ![0, 0, 0]], ![![4, 1, 0], ![0, 0, 0]]], ![![![3, 1, -1], ![9, 0, 0]], ![![-1, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-7, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
