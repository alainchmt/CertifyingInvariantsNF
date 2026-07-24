import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_557179_1.RI3_1_557179_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![32, -1, -3]

def alpha1 := B.equivFun.symm ![-837, 76, -63]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-1409, -97, 25]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![0, 1, 9]]]
 hmul := by decide
 f := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![324, 86, 0], ![-176, 4, 0]], ![![0, 0, 0], ![-9, 1, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, 12, 0], ![-48, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![8, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![0, 2, 0], ![0, 1, 9]]]
 hmul := by decide
 f := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![162, 2822, 18], ![-5696, 52, 0]], ![![108, -108, 0], ![-9, 1, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, 7, 72], ![8, -63, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![16, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![0, 8, 0]], ![![0, 2, 0], ![0, 1, 9]]]
 hmul := by decide
 f := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![81, 6912, 18], ![-13884, 60, 0]], ![![252, -252, 0], ![-9, 1, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![8, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, -5, -45], ![0, 81, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![32, 0, 0], ![16, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![0, 16, 0]], ![![0, 2, 0], ![0, 1, 9]]]
 hmul := by decide
 f := ![![![![2512, 1058636, 1917], ![-2121589, 4317, 0]], ![![37665, -37665, 0], ![-620, 62, 0]]], ![![![1256, 527420, 954], ![-1056991, 2151, 0]], ![![18765, -18765, 0], ![-309, 31, 0]]]]
 g := ![![![![-15, 237, 126], ![32, -448, 0]], ![![8, -1903, -1008], ![-16, 3584, 0]]], ![![![-1, -238, -126], ![2, 448, 0]], ![![-8, -239, -126], ![16, 449, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![16, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![32, -1, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![0, 32, 0]], ![![32, 2, 0], ![0, 17, 9]]]
 hmul := by decide
 f := ![![![![124758365, -416115252, -371073], ![833065405, -834901, 0]], ![![-249514218, 14676453, 0], ![1613, 62, 0]]]]
 g := ![![![![1235, -112, 93]], ![![-6696, 608, -504]]], ![![![199, -18, 15]], ![![-1080, 98, -81]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 0, 0], ![-3, -2, 3]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![6, 0, 0], ![-3, -2, 3]] ![![6, 0, 0], ![-3, -2, 3]]
  ![![-837, 76, -63]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![36, 0, 0], ![-18, -12, 18]], ![![-18, -12, 18], ![1881, -140, 27]]]
 hmul := by decide
 f := ![![![![-54458160, 10911255, -10168422], ![18507787, 0, 0]], ![![0, 0, 0], ![1219369, 0, 0]]]]
 g := ![![![![-4, -3, -2]], ![![106, 19, 7]]], ![![![106, 19, 7]], ![![-1029, -100, -4]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1615823, -146673, 121706])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![-3, -2, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![6, 0, 0], ![-3, -2, 3]]
  ![![6, 0, 0], ![0, 2, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![12, 0, 0], ![-6, -4, 6]], ![![0, 6, 0], ![-432, -2, -18]]]
 hmul := by decide
 f := ![![![![-1, -56, -48], ![-3, 0, 0]], ![![99, 11, 0], ![0, 0, 0]]], ![![![2, 3, -2], ![4, 0, 0]], ![![-3, 0, 0], ![0, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-1, -1, 1], ![1, 0, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![-72, 0, -3], ![-1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![0, 2, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![0, 1, 0]] ![![6, 0, 0], ![-3, -2, 3]]
  ![![12, 0, 0], ![0, 2, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![24, 0, 0], ![-12, -8, 12]], ![![0, 6, 0], ![-432, -2, -18]]]
 hmul := by decide
 f := ![![![![-37, 205, -66], ![-75, 0, 0]], ![![-966, 46, 0], ![0, 0, 0]]], ![![![1, -1, -1], ![2, 0, 0]], ![![7, 0, 0], ![0, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-1, 4, 1], ![-28, 0, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![-36, -6, -51], ![2, 33, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![0, 2, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![8, 0, 0], ![0, 1, 0]] ![![6, 0, 0], ![-3, -2, 3]]
  ![![24, 0, 0], ![0, 2, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![48, 0, 0], ![-24, -16, 24]], ![![0, 6, 0], ![-432, -2, -18]]]
 hmul := by decide
 f := ![![![![-49, 155, -162], ![-99, 0, 0]], ![![-1692, 188, 0], ![0, 0, 0]]], ![![![2, 1, -2], ![4, 0, 0]], ![![3, 0, 0], ![0, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-1, -9, -68], ![8, 92, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![-18, 5, 51], ![8, -69, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0], ![0, 2, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![0, 1, 0]] ![![6, 0, 0], ![-3, -2, 3]]
  ![![48, 0, 0], ![0, 2, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![96, 0, 0], ![-48, -32, 48]], ![![0, 6, 0], ![-432, -2, -18]]]
 hmul := by decide
 f := ![![![![431, -3273, -30], ![861, 0, 0]], ![![57672, -712, 0], ![0, 0, 0]]], ![![![1, -1, -1], ![2, 0, 0]], ![![27, 0, 0], ![0, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-1, -2, -8], ![8, 24, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![-9, 0, -3], ![-8, 7, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![48, 0, 0], ![0, 2, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![16, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![16, 1, 0]] ![![6, 0, 0], ![-3, -2, 3]]
  ![![96, 0, 0], ![0, 2, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![192, 0, 0], ![-96, -64, 96]], ![![96, 6, 0], ![-480, -34, 30]]]
 hmul := by decide
 f := ![![![![-33862, 1905, -6489], ![13059, 0, 0]], ![![80784, -144, 0], ![0, 0, 0]]], ![![![-33869, 1904, -6488], ![13057, 0, 0]], ![![80795, -144, 0], ![0, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-1, -31, -272], ![0, 1456, 0]]], ![![![1, 0, 0], ![3, 0, 0]], ![![-5, -10, -85], ![8, 455, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![96, 0, 0], ![0, 2, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
