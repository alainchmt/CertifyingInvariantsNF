import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_933907_1.RI3_1_933907_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![4376, -880, 101]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![5263355991, -314273128, -66970992]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-80, 4, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-80, 4, 1]] ![![3, 0, 0], ![-80, 4, 1]]
  ![![9, 0, 0], ![-80, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-240, 12, 3]], ![![-240, 12, 3], ![745, -65, -11]]]
 hmul := by decide
 f := ![![![![51, -58, -4], ![-54, 0, 0]], ![![0, 0, 0], ![-18, 0, 0]]], ![![![80, 489, 29], ![500, 0, 0]], ![![0, 0, 0], ![160, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![3, 0, 0]]], ![![![0, 1, 0], ![3, 0, 0]], ![![65, -7, -1], ![-2, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-80, 1, 1]] ![![3, 0, 0], ![-80, 4, 1]]
  ![![27, 0, 0], ![-89, 10, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![-720, 36, 9]], ![![-240, 3, 3], ![3007, -188, -35]]]
 hmul := by decide
 f := ![![![![1615, 17889, -15], ![-18210, 0, 0]], ![![54135, 0, 0], ![-54, 0, 0]]], ![![![-5125, -58977, 47], ![60033, 0, 0]], ![![-178445, 0, 0], ![178, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![3, -2, 0], ![9, 0, 0]]], ![![![1, -1, 0], ![3, 0, 0]], ![![85, -4, -1], ![-8, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![27, 0, 0], ![-89, 10, 1]] ![![3, 0, 0], ![-80, 4, 1]]
  ![![81, 0, 0], ![-89, 37, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0, 0], ![-2160, 108, 27]], ![![-267, 30, 3], ![-3059, 145, 28]]]
 hmul := by decide
 f := ![![![![-440, -16953, 360], ![-10344, 0, 0]], ![![82620, 0, 0], ![81, 0, 0]]], ![![![520, 18626, -396], ![11367, 0, 0]], ![![-90780, 0, 0], ![-89, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![3, -11, 0], ![27, 0, 0]]], ![![![0, -1, 0], ![3, 0, 0]], ![![-7, -11, 0], ![28, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![81, 0, 0], ![-89, 37, 1]] ![![3, 0, 0], ![-80, 4, 1]]
  ![![243, 0, 0], ![-89, 37, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![243, 0, 0], ![-6480, 324, 81]], ![![-267, 111, 3], ![-23417, 1252, 244]]]
 hmul := by decide
 f := ![![![![-350002, -7605140, 30769], ![-795579, 0, 0]], ![![18968580, 0, 0], ![243, 0, 0]]], ![![![128246, 2785419, -11270], ![291387, 0, 0]], ![![-6947340, 0, 0], ![-89, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![3, -11, 0], ![81, 0, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![-7, -32, 0], ![244, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![243, 0, 0], ![-89, 37, 1]] ![![3, 0, 0], ![-80, 4, 1]]
  ![![4376, -880, 101]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![729, 0, 0], ![-19440, 972, 243]], ![![-267, 111, 3], ![-23417, 1252, 244]]]
 hmul := by decide
 f := ![![![![-2101168, -45651696, 184701], ![-4775664, 0, 0]], ![![341590560, 0, 0], ![4376, 0, 0]]]]
 g := ![![![![-359, 7, 3]], ![![5175, -292, -64]]], ![![![-230, -4, 1]], ![![6259, -331, -75]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-182817440880461721, 36756540018842280, -4221875763823376])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-80, 4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-80, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-89, 10, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![-89, 37, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![243, 0, 0], ![-89, 37, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
