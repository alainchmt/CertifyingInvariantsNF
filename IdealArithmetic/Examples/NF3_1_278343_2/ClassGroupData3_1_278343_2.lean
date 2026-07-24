import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_278343_2.RI3_1_278343_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![546, 22, 31]

def alpha1 := B.equivFun.symm ![83165166, 3352393, 4721968]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-186405099, 35400590, 10903160]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![10, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![10, 0, 1]] ![![2, 0, 0], ![10, 0, 1]]
  ![![4, 0, 0], ![12, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![20, 0, 2]], ![![20, 0, 2], ![76, 12, 5]]]
 hmul := by decide
 f := ![![![![87394, -109085, -191995], ![341006, -44076, 0]], ![![0, 0, 0], ![-364, -4, 0]]], ![![![262423, -327537, -576480], ![1023897, -132342, 0]], ![![0, 0, 0], ![-1093, -12, 0]]]]
 g := ![![![![16, -9, -22], ![76, -12, 0]], ![![122, -45, -106], ![366, -60, 0]]], ![![![122, -45, -106], ![366, -60, 0]], ![![493, -168, -401], ![1381, -228, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![12, 0, 1]] ![![2, 0, 0], ![10, 0, 1]]
  ![![546, 22, 31]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![40, 0, 4]], ![![24, 0, 2], ![96, 12, 7]]]
 hmul := by decide
 f := ![![![![52551126206, -66426409405, -115720830496], ![204895215794, -26546445198, 0]], ![![-79527051, -81520992, 0], ![-562751, -546, 0]]]]
 g := ![![![![-13, 4, -3]], ![![133, -28, -1]]], ![![![60, -12, -2]], ![![-162, 18, 41]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![2, 1, 8]]]
 hmul := by decide
 f := ![![![![-4389, -29592, -16910], ![54854, 4420, 6]], ![![0, 0, 0], ![-324, 0, 4]]], ![![![-2187, -14742, -8425], ![27327, 2202, 3]], ![![0, 0, 0], ![-161, 0, 2]]]]
 g := ![![![![7570, -2487, 113], ![3168, 0, -452]], ![![-68, 22, -1], ![-26, 0, 4]]], ![![![-68, 22, -1], ![-26, 0, 4]], ![![3752, -1232, 58], ![1569, 0, -224]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![4, 0, 0], ![2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![83165166, 3352393, 4721968]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![4, 2, 0], ![2, 3, 8]]]
 hmul := by decide
 f := ![![![![-18375287220387, -133747887105882, -73745276964249], ![249228780858993, 18439706718006, 11514224349]], ![![-279828606157, 0, -19221210525], ![-4244775859, 0, -83165166]]]]
 g := ![![![![-5029, 499, 1416]], ![![57847, -12885, 1288]]], ![![![26409, -6193, 1352]], ![![48563, -32, -25448]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![230180718289647701, 9278599031783710, 13069245674052840])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![10, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![10, 0, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0], ![11, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![20, 0, 2], ![81, -5, -1]]]
 hmul := by decide
 f := ![![![![-19122, -138894, -76958], ![258929, 19274, 28]], ![![-249, 0, 0], ![-2, 0, 0]]], ![![![-105108, -763107, -422825], ![1422616, 105896, 155]], ![![-1368, 0, 0], ![-11, 0, 0]]]]
 g := ![![![![-9, -1, -1], ![2, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![-1, -1, 0], ![2, 0, 0]], ![![2, -6, -4], ![7, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![11, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![10, 0, 1]] ![![4, 0, 0], ![2, 1, 0]]
  ![![4, 0, 0], ![-9, 1, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![8, 0, 0], ![4, 2, 0]], ![![40, 0, 4], ![101, -5, 1]]]
 hmul := by decide
 f := ![![![![698677364, -229414681, 10428928], ![291985014, 0, -41711580]], ![![-2065, 0, 0], ![-4, 0, 0]]], ![![![-1570256558, 515602657, -23438705], ![-656227610, 0, 93745533]], ![![4641, 0, 0], ![9, 0, 0]]]]
 g := ![![![![146, -154, -44], ![-356, 0, -36]], ![![64, -64, -18], ![-147, 0, -15]]], ![![![730, -770, -219], ![-1780, 0, -180]], ![![1877, -1978, -564], ![-4567, 0, -462]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-9, 1, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![12, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![12, 0, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![11, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![24, 0, 2], ![81, -3, -1]]]
 hmul := by decide
 f := ![![![![-4557425, -33147459, -18281407], ![61763837, 4573210, 2858]], ![![-40510, -492, 0], ![-4, 0, 0]]], ![![![-12532808, -91155132, -50273664], ![169849820, 12576276, 7858]], ![![-111402, -1353, 0], ![-11, 0, 0]]]]
 g := ![![![![86, 12, -138], ![228, -36, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![273, 33, -400], ![657, -105, 0]], ![![965, 113, -1395], ![2285, -366, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![11, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![12, 0, 1]] ![![4, 0, 0], ![2, 1, 0]]
  ![![4, 0, 0], ![9, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![16, 0, 0], ![8, 4, 0]], ![![48, 0, 4], ![105, -3, 1]]]
 hmul := by decide
 f := ![![![![1044908285, -343103728, 15595844], ![436678213, 0, -62382446]], ![![-927, 0, 0], ![-12, 0, 0]]], ![![![2351317597, -772073343, 35094738], ![982640467, 0, -140376859]], ![![-2086, 0, 0], ![-27, 0, 0]]]]
 g := ![![![![-5, -1, -1], ![4, 0, 0]], ![![-7, 0, -1], ![4, 0, 0]]], ![![![-6, -2, -1], ![8, 0, 0]], ![![-3, -4, -3], ![13, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![9, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
