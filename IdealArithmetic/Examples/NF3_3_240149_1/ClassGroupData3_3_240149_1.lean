import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_240149_1.RI3_3_240149_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-3, 2, 1]

def alpha1 := B.equivFun.symm ![-4, 2, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-26, 0, 1]

def zeta2 := B.equivFun.symm ![-64, 0, 3]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![1, 0, 5]]]
 hmul := by decide
 f := ![![![![0, 0, -5], ![0, 2, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![-51, 48, 50], ![-35, 102, 0]], ![![0, 0, 0], ![-243, -1, 0]]]]
 g := ![![![![-4, -10, -25], ![0, 20, 0]], ![![0, 2, 5], ![2, -4, 0]]], ![![![0, 2, 5], ![2, -4, 0]], ![![-2, -3, -5], ![2, 5, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![-3, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![4, 2, 0], ![1, 2, 5]]]
 hmul := by decide
 f := ![![![![-347, 0, 102], ![0, 83, 0]], ![![611, 0, 0], ![-489, -2, 0]]]]
 g := ![![![![10, -3, 1]], ![![-26, 17, -7]]], ![![![-8, 7, -3]], ![![77, -40, 16]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![9, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![1, 0, 5]]]
 hmul := by decide
 f := ![![![![0, 0, -5], ![0, 2, 0]], ![![0, 0, 0], ![3, 0, 0]]], ![![![-40, 48, 75], ![-63, 120, 0]], ![![0, 0, 0], ![-493, -2, 0]]]]
 g := ![![![![-6, 29, -50], ![9, 90, 0]], ![![0, 3, -5], ![3, 9, 0]]], ![![![0, 3, -5], ![3, 9, 0]], ![![0, 3, -5], ![3, 10, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![9, 0, 0], ![-3, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![-4, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![27, 0, 0], ![0, 9, 0]], ![![-9, 3, 0], ![1, -3, 5]]]
 hmul := by decide
 f := ![![![![-297, 0, 88], ![0, 57, 0]], ![![-834, 0, 0], ![-996, -4, 0]]]]
 g := ![![![![33, 1, -2]], ![![33, -5, 1]]], ![![![0, -2, 1]], ![![-17, 8, -3]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![9, -5, 2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-109, 45, 24])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![6, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![6, 0, 0], ![0, 2, 0]], ![![0, 3, 0], ![1, 0, 5]]]
 hmul := by decide
 f := ![![![![2, 0, 5], ![0, 6, 0]], ![![0, -6, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]]
 g := ![![![![0, 0, -5], ![0, 6, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![0, 1, 0]] ![![9, 0, 0], ![-3, 1, 0]]
  ![![18, 0, 0], ![6, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![18, 0, 0], ![-6, 2, 0]], ![![0, 9, 0], ![1, -3, 5]]]
 hmul := by decide
 f := ![![![![-69, 293, -455], ![63, 900, 0]], ![![0, -18, 0], ![0, 0, 0]]], ![![![-24, 103, -160], ![23, 315, 0]], ![![-1, -6, 0], ![0, 0, 0]]]]
 g := ![![![![-30, -221, -185], ![-18, 666, 0]], ![![6, 77, 65], ![20, -234, 0]]], ![![![0, 18, 15], ![9, -54, 0]], ![![-6, -19, -15], ![9, 55, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![18, 0, 0], ![6, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![2, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![12, 0, 0], ![6, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![12, 0, 0], ![0, 4, 0]], ![![6, 3, 0], ![1, 2, 5]]]
 hmul := by decide
 f := ![![![![3400, 3240, -465], ![-4320, 360, 0]], ![![-6984, -108, 0], ![0, 0, 0]]], ![![![1762, 1680, -245], ![-2240, 189, 0]], ![![-3621, -56, 0], ![0, 0, 0]]]]
 g := ![![![![-24, -220, -185], ![-24, 444, 0]], ![![0, 12, 10], ![4, -24, 0]]], ![![![-12, -101, -85], ![-9, 204, 0]], ![![-6, -13, -10], ![8, 25, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![6, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![2, 1, 0]] ![![9, 0, 0], ![-3, 1, 0]]
  ![![36, 0, 0], ![6, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![36, 0, 0], ![-12, 4, 0]], ![![18, 9, 0], ![-5, -1, 5]]]
 hmul := by decide
 f := ![![![![-1753386, 7232726, -12133985], ![1388106, 21843360, 0]], ![![-421416, -972, 0], ![0, 0, 0]]], ![![![-295836, 1220334, -2047295], ![234214, 3685500, 0]], ![![-71103, -164, 0], ![0, 0, 0]]]]
 g := ![![![![-36, -222, -185], ![0, 1332, 0]], ![![6, 77, 65], ![40, -468, 0]]], ![![![-18, -102, -85], ![9, 612, 0]], ![![0, 29, 25], ![29, -179, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![36, 0, 0], ![6, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
