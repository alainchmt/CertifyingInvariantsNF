import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_767839_1.RI3_1_767839_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![216202, 17609, 4956]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-1466016, 332843, 22449]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![9, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![1, -2, 1]]]
 hmul := by decide
 f := ![![![![0, 242, -118], ![0, -120, 0]], ![![0, 0, 0], ![1404, -9, 0]]], ![![![0, 28, -14], ![0, -11, 0]], ![![0, 0, 0], ![157, -1, 0]]]]
 g := ![![![![7, 3, 0], ![-27, 0, 0]], ![![-5, -4, -1], ![21, 9, 0]]], ![![![-5, -4, -1], ![21, 9, 0]], ![![-1, -1, 0], ![5, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![2, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![27, 0, 0], ![-7, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 9, 0]], ![![6, 3, 0], ![-2, 1, 1]]]
 hmul := by decide
 f := ![![![![15318, -23806, -9316], ![24894, -273, 0]], ![![-33696, 87480, 0], ![-8424, -27, 0]]], ![![![-4534, 7047, 2757], ![-7367, 83, 0]], ![![9976, -25896, 0], ![2494, 8, 0]]]]
 g := ![![![![43, -6, 0], ![162, 0, 0]], ![![-5, 8, -1], ![-18, 27, 0]]], ![![![22, -3, 0], ![84, 0, 0]], ![![2, 0, 0], ![8, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![27, 0, 0], ![-7, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![81, 0, 0], ![-7, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0, 0], ![-27, 27, 0]], ![![-21, 3, 0], ![7, -8, 1]]]
 hmul := by decide
 f := ![![![![-137846, 443449, -20359], ![-223998, -108651, 0]], ![![-252720, 1535760, 0], ![-25272, -81, 0]]], ![![![13604, -43763, 2009], ![22107, 10723, 0]], ![![24940, -151560, 0], ![2494, 8, 0]]]]
 g := ![![![![435, -62, 0], ![5022, 0, 0]], ![![-131, 26, -1], ![-1512, 81, 0]]], ![![![-105, 22, -1], ![-1212, 81, 0]], ![![49, -7, 0], ![566, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![81, 0, 0], ![-7, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![243, 0, 0], ![-88, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![243, 0, 0], ![-81, 81, 0]], ![![-21, 3, 0], ![7, -8, 1]]]
 hmul := by decide
 f := ![![![![-137846, 1500278, -66308], ![-223998, -476244, 0]], ![![-758160, 18254160, 0], ![-75816, -243, 0]]], ![![![50484, -549445, 24283], ![82037, 174417, 0]], ![![277660, -6685200, 0], ![27766, 89, 0]]]]
 g := ![![![![7745, -88, 0], ![21384, 0, 0]], ![![-2523, 117, -1], ![-6966, 243, 0]]], ![![![-615, 95, -1], ![-1698, 243, 0]], ![![381, -4, 0], ![1052, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![243, 0, 0], ![-88, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![216202, 17609, 4956]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![729, 0, 0], ![-243, 243, 0]], ![![-264, 3, 0], ![88, -89, 1]]]
 hmul := by decide
 f := ![![![![33252525510, -351594464964, -28094519198], ![54035353955, 96749140088, 0]], ![![42064444769, -1009697406543, 0], ![-61996234, -198593, 0]]]]
 g := ![![![![6047, -938, -215]], ![![-13124, 4550, -241]]], ![![![-2327, 392, 74]], ![![4599, -1671, 106]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![6950122447759, 566066591643, 159317741464])
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

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-7, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![-7, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![243, 0, 0], ![-88, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
