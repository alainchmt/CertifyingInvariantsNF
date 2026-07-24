import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_58604_2.RI3_1_58604_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-3, 1, 0]

def alpha1 := B.equivFun.symm ![19, 2, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![19, -13, 2]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![9, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![0, 0, 1]]]
 hmul := by decide
 f := ![![![![15, -5, 0], ![1, 0, 0]], ![![0, 0, 0], ![0, -3, 0]]], ![![![-5, 1, 0], ![2, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![3, 0, 0]]], ![![![1, 0, 0], ![3, 0, 0]], ![![1, 0, 0], ![3, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-3, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![0, 9, 0]], ![![-9, 3, 0], ![0, -3, 1]]]
 hmul := by decide
 f := ![![![![-4, 0, 0], ![-4, 3, 0]], ![![-7, -9, 0], ![3, 1, 0]]]]
 g := ![![![![-23, -3, -1]], ![![-14, -3, -1]]], ![![![3, 0, 0]], ![![0, 1, 0]]]]
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
 f := ![![![![0, -340, -111], ![0, -150, 0]], ![![0, 0, 0], ![1521, -36, 0]]], ![![![0, -133, -44], ![0, -56, 0]], ![![0, 0, 0], ![592, -14, 0]]]]
 g := ![![![![5, 1, 0], ![-9, 0, 0]], ![![-1, 0, 0], ![3, 0, 0]]], ![![![-1, 0, 0], ![3, 0, 0]], ![![-3, -1, 0], ![7, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![9, 0, 0], ![4, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![19, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![12, 3, 0], ![4, 5, 1]]]
 hmul := by decide
 f := ![![![![27387, 27387, 22430], ![18258, -64507, 0]], ![![-73032, -6200, 0], ![-6086, -72, 0]]]]
 g := ![![![![-3, 4, -1]], ![![-15, 5, 1]]], ![![![-6, 3, 0]], ![![-2, -1, 1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-3539, -415, -187])
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

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0], ![9, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![0, 3, 0], ![0, 1, 1]]]
 hmul := by decide
 f := ![![![![0, -1, 0], ![1, 0, 0]], ![![2, 0, 0], ![0, 0, 0]]], ![![![0, -3, 0], ![3, 0, 0]], ![![6, 0, 0], ![1, 0, 0]]]]
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![-8, 0, -1], ![3, 0, 0]]], ![![![-9, 0, -1], ![3, 0, 0]], ![![-3, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![9, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![0, 1, 0]] ![![9, 0, 0], ![4, 1, 0]]
  ![![9, 0, 0], ![-12, 2, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![27, 0, 0], ![12, 3, 0]], ![![0, 9, 0], ![0, 4, 1]]]
 hmul := by decide
 f := ![![![![359, 125, -2], ![-807, 18, 0]], ![![-130, 0, 0], ![0, 0, 0]]], ![![![476, 168, -3], ![-1072, 28, 0]], ![![-182, 0, 0], ![-4, 0, 0]]]]
 g := ![![![![39, 4, -8], ![-36, 18, 0]], ![![4, 1, -1], ![-5, 2, 0]]], ![![![-24, -5, 9], ![45, -18, 0]], ![![-12, -2, 4], ![19, -8, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-12, 2, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![9, 0, 0], ![-3, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![9, 0, 0], ![33, 7, 4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![-9, 3, 0], ![-3, -2, 1]]]
 hmul := by decide
 f := ![![![![2, -1, 0], ![1, 0, 0]], ![![7, 1, 0], ![-3, 0, 0]]], ![![![38, 10, 2], ![-44, -6, 0]], ![![70, 5, 0], ![-11, 0, 0]]]]
 g := ![![![![159, -436, -88], ![324, -72, 0]], ![![94, -292, -60], ![219, -48, 0]]], ![![![-65, 91, 16], ![-64, 16, 0]], ![![-57, 92, 17], ![-66, 16, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![33, 7, 4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![9, 0, 0], ![-3, 1, 0]] ![![9, 0, 0], ![4, 1, 0]]
  ![![9, 0, 0], ![6, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![81, 0, 0], ![36, 9, 0]], ![![-27, 9, 0], ![-12, 1, 1]]]
 hmul := by decide
 f := ![![![![-16995, -5899, -432], ![37939, 3888, 0]], ![![-400, 0, 0], ![0, 0, 0]]], ![![![-33982, -11792, -863], ![75860, 7767, 0]], ![![-800, 0, 0], ![1, 0, 0]]]]
 g := ![![![![9, 0, 0], ![0, 0, 0]], ![![-2, 0, -1], ![9, 0, 0]]], ![![![-3, 1, 0], ![0, 0, 0]], ![![-2, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![6, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
