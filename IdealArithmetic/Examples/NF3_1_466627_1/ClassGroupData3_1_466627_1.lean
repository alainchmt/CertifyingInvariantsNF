import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_466627_1.RI3_1_466627_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![4, 1, 0]

def alpha1 := B.equivFun.symm ![5, 1, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-707, -54, 9]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![0, 0, 1]]]
 hmul := by decide
 f := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![103, 21, 0], ![12, 0, 0]], ![![0, 0, 0], ![1, -1, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![8, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![0, 2, 0], ![0, 0, 1]]]
 hmul := by decide
 f := ![![![![-514, 0, 0], ![-343, -6, 6]], ![![151, 0, 0], ![14, -14, 0]]], ![![![-51, 0, 0], ![-214, -2, 2]], ![![375, 0, 0], ![7, -7, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-2, 0, 0], ![4, 0, 0]]], ![![![-1, 0, 0], ![2, 0, 0]], ![![2, 0, 0], ![-4, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![4, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![16, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![0, 8, 0]], ![![8, 2, 0], ![0, 4, 1]]]
 hmul := by decide
 f := ![![![![143, 0, 0], ![7, -2, 2]], ![![334, 0, 0], ![140, -28, 0]]], ![![![28, 0, 0], ![0, 0, 0]], ![![305, 0, 0], ![35, -7, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-2, 0, 0], ![8, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![4, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![32, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![0, 16, 0]], ![![8, 2, 0], ![0, 4, 1]]]
 hmul := by decide
 f := ![![![![259, 0, 0], ![65, -2, 2]], ![![204, 113, 0], ![54, -56, 0]]], ![![![14, 0, 0], ![0, 0, 0]], ![![305, 14, 0], ![7, -7, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-2, 0, 0], ![16, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![4, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![0, 32, 0]], ![![8, 2, 0], ![0, 4, 1]]]
 hmul := by decide
 f := ![![![![7, 0, 0], ![0, 0, 0]], ![![305, 14, 0], ![7, -7, 0]]]]
 g := ![![![![-87, -5, 1]], ![![206, 10, -2]]], ![![![2, 0, 0]], ![![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![9, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![1, -2, 1]]]
 hmul := by decide
 f := ![![![![0, 1622, -583], ![0, -732, 0]], ![![0, 0, 0], ![7425, -18, 0]]], ![![![0, -900, 323], ![0, 409, 0]], ![![0, 0, 0], ![-4124, 10, 0]]]]
 g := ![![![![37, -9, 0], ![81, 0, 0]], ![![-7, 6, -1], ![-15, 9, 0]]], ![![![-7, 6, -1], ![-15, 9, 0]], ![![5, -1, 0], ![11, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![9, 0, 0], ![-4, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 9, 0]], ![![-12, 3, 0], ![4, -5, 1]]]
 hmul := by decide
 f := ![![![![79224, -151438, 17408], ![128739, 29874, 0]], ![![79224, -244104, 0], ![-6602, -8, 0]]]]
 g := ![![![![-77, -6, 1]], ![![163, 12, -2]]], ![![![80, 6, -1]], ![![-164, -11, 2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![4201, 1431, 126])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![6, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![6, 0, 0], ![-2, 2, 0]], ![![0, 3, 0], ![0, -1, 1]]]
 hmul := by decide
 f := ![![![![2, 1, 0], ![3, 6, 0]], ![![0, -4, 0], ![0, 0, 0]]], ![![![0, 1, 1], ![-1, 0, 0]], ![![-1, -2, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-1, 0, 0], ![2, 0, 0]]], ![![![-1, 0, 0], ![3, 0, 0]], ![![1, 0, 0], ![-3, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![0, 1, 0]] ![![9, 0, 0], ![-4, 1, 0]]
  ![![18, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![18, 0, 0], ![-8, 2, 0]], ![![0, 9, 0], ![0, -4, 1]]]
 hmul := by decide
 f := ![![![![81, -20, 5], ![180, 0, 0]], ![![0, -10, 0], ![0, 0, 0]]], ![![![-18, 9, -2], ![-40, 9, 0]], ![![-1, 2, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![2, 0, 0], ![9, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![18, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![12, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![12, 0, 0], ![-4, 4, 0]], ![![0, 3, 0], ![0, -1, 1]]]
 hmul := by decide
 f := ![![![![2, 1, 0], ![3, 6, 0]], ![![0, -8, 0], ![0, 0, 0]]], ![![![0, -1, 0], ![1, 0, 0]], ![![3, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![4, 0, 0]]], ![![![1, 0, 0], ![3, 0, 0]], ![![1, 0, 0], ![3, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![0, 1, 0]] ![![9, 0, 0], ![-4, 1, 0]]
  ![![36, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![36, 0, 0], ![-16, 4, 0]], ![![0, 9, 0], ![0, -4, 1]]]
 hmul := by decide
 f := ![![![![161, -44, 6], ![360, -9, 0]], ![![0, -20, 0], ![0, 0, 0]]], ![![![-25, 11, -1], ![-56, 9, 0]], ![![-3, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![1, 0, 0], ![9, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![36, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![8, 0, 0], ![4, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![24, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![24, 0, 0], ![-8, 8, 0]], ![![12, 3, 0], ![-4, 3, 1]]]
 hmul := by decide
 f := ![![![![-2380, 1148, -122], ![-3867, 372, 0]], ![![2184, -16, 0], ![0, 0, 0]]], ![![![146, -70, 7], ![239, -21, 0]], ![![-133, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![8, 0, 0]]], ![![![1, 0, 0], ![3, 0, 0]], ![![1, 0, 0], ![7, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![8, 0, 0], ![4, 1, 0]] ![![9, 0, 0], ![-4, 1, 0]]
  ![![72, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![72, 0, 0], ![-32, 8, 0]], ![![36, 9, 0], ![-16, 0, 1]]]
 hmul := by decide
 f := ![![![![2909209, -826810, 26021], ![6525306, -234144, 0]], ![![-18144, -40, 0], ![0, 0, 0]]], ![![![-70729, 20104, -633], ![-158644, 5697, 0]], ![![441, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![8, 0, 0]]], ![![![1, 0, 0], ![9, 0, 0]], ![![0, 0, 0], ![4, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![72, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![4, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![48, 0, 0], ![20, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![48, 0, 0], ![-16, 16, 0]], ![![12, 3, 0], ![-4, 3, 1]]]
 hmul := by decide
 f := ![![![![1182, -560, 64], ![1923, -186, 0]], ![![-2160, -32, 0], ![0, 0, 0]]], ![![![222, -102, 12], ![361, -33, 0]], ![![-405, -16, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-7, 0, 0], ![16, 0, 0]]], ![![![-1, 0, 0], ![3, 0, 0]], ![![7, 0, 0], ![-17, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![48, 0, 0], ![20, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![16, 0, 0], ![4, 1, 0]] ![![9, 0, 0], ![-4, 1, 0]]
  ![![144, 0, 0], ![68, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![144, 0, 0], ![-64, 16, 0]], ![![36, 9, 0], ![-16, 0, 1]]]
 hmul := by decide
 f := ![![![![44211297, -12598940, 395080], ![99322326, -3555513, 0]], ![![-272160, -368, 0], ![0, 0, 0]]], ![![![21074924, -6005742, 188329], ![47345602, -1694862, 0]], ![![-129735, -176, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-8, 0, 0], ![16, 0, 0]]], ![![![-4, 0, 0], ![9, 0, 0]], ![![32, 0, 0], ![-68, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![144, 0, 0], ![68, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![4, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![96, 0, 0], ![-28, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![96, 0, 0], ![-32, 32, 0]], ![![12, 3, 0], ![-4, 3, 1]]]
 hmul := by decide
 f := ![![![![92712, -44529, 4793], ![150657, -14463, 0]], ![![-339936, 896, 0], ![0, 0, 0]]], ![![![-33000, 15850, -1707], ![-53623, 5151, 0]], ![![121003, -320, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![9, 0, 0], ![32, 0, 0]]], ![![![1, 0, 0], ![3, 0, 0]], ![![9, 0, 0], ![31, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![96, 0, 0], ![-28, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![32, 0, 0], ![4, 1, 0]] ![![9, 0, 0], ![-4, 1, 0]]
  ![![288, 0, 0], ![68, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![288, 0, 0], ![-128, 32, 0]], ![![36, 9, 0], ![-16, 0, 1]]]
 hmul := by decide
 f := ![![![![-1392613999, 397377004, -12439471], ![-3130986006, 111952935, 0]], ![![8517312, 8192, 0], ![0, 0, 0]]], ![![![-302855078, 86418526, -2705243], ![-680902972, 24346683, 0]], ![![1852281, 1792, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-8, 0, 0], ![32, 0, 0]]], ![![![-2, 0, 0], ![9, 0, 0]], ![![16, 0, 0], ![-68, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![288, 0, 0], ![68, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl
