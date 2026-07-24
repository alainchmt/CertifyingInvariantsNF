import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_32780_1.RI3_1_32780_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![7, 1, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![627, 690, -542]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![9, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![-1, -4, 5]]]
 hmul := by decide
 f := ![![![![-3128, -5476, 8935], ![-780, -4302, 0]], ![![0, 0, 0], ![-3213, -18, 0]]], ![![![-348, -610, 995], ![-86, -479, 0]], ![![0, 0, 0], ![-358, -2, 0]]]]
 g := ![![![![77, -2, -200], ![18, 360, 0]], ![![-31, 1, 80], ![-6, -144, 0]]], ![![![-31, 1, 80], ![-6, -144, 0]], ![![-3, -1, 5], ![5, -8, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![2, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![27, 0, 0], ![11, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 9, 0]], ![![6, 3, 0], ![-4, -1, 5]]]
 hmul := by decide
 f := ![![![![2905956, 5085423, -10327520], ![726489, 6061392, 0]], ![![6610248, 399168, 0], ![18630, -54, 0]]], ![![![1076572, 1884001, -3826045], ![269143, 2245569, 0]], ![![2448904, 147880, 0], ![6902, -20, 0]]]]
 g := ![![![![-99, 450, 250], ![0, -1350, 0]], ![![36, -180, -100], ![9, 540, 0]]], ![![![-21, 90, 50], ![3, -270, 0]], ![![7, -64, -35], ![17, 190, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![27, 0, 0], ![11, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![7, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0, 0], ![-27, 27, 0]], ![![33, 3, 0], ![-13, 8, 5]]]
 hmul := by decide
 f := ![![![![-26809781, -46917118, 81321656], ![-6702444, -49063307, 0]], ![![-19519772, 2431624, 0], ![3710, -12, 0]]]]
 g := ![![![![-1, -5, 4]], ![![49, 2, -7]]], ![![![5, -2, 1]], ![![11, 3, -3]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow4 : J0 ^ 4 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-11623629, -1125714, -1811942])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![11, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
