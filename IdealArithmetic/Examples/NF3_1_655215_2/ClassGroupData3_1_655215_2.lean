import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_655215_2.RI3_1_655215_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-11070051142961, -451985185477, -288776127796]

def alpha1 := B.equivFun.symm ![-82737112268, -3378118904, -2158301041]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![6477391982957248836881, -2053720924028759695462, -14553435996272430146]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![1, 3, 2]]]
 hmul := by decide
 f := ![![![![224908, -105020, 1573], ![59944, 0, -4248]], ![![0, 0, 0], ![964, 0, -4]]], ![![![158, -75, 1], ![44, 0, -3]], ![![0, 0, 0], ![1, 0, 0]]]]
 g := ![![![![107, 107, 157], ![56, -312, -4]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-54, -54, -78], ![-23, 156, 2]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![-11070051142961, -451985185477, -288776127796]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![2, 2, 0], ![1, 3, 2]]]
 hmul := by decide
 f := ![![![![-324522664990188934445, 151093548477213471502, -3067754240295439006], ![-86714558256487731470, 0, 6131332401973880003]], ![![-1353329040288532680, 0, 11277742002404439], ![-2559405880939121, 0, 10618065957484]]]]
 g := ![![![![3342632, -1079563, 11030]], ![![2333116, 398728, -1074048]]], ![![![1166558, 199364, -537024]], ![![-31638161, 10180563, -69148]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![24, 2, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![2, 0, 0], ![24, 2, 1]] ![![2, 0, 0], ![24, 2, 1]]
  ![![4, 0, 0], ![24, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![48, 4, 2]], ![![48, 4, 2], ![996, 20, 21]]]
 hmul := by decide
 f := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![-45, 265, 8], ![-125, 30, 0]], ![![0, 0, 0], ![-1, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-24, 12, 4], ![-14, 4, 0]]], ![![![-24, 12, 4], ![-14, 4, 0]], ![![-21, 60, 19], ![-55, 20, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![4, 0, 0], ![24, 0, 1]] ![![2, 0, 0], ![24, 2, 1]]
  ![![-82737112268, -3378118904, -2158301041]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![8, 0, 0], ![96, 8, 4]], ![![48, 0, 2], ![756, 38, 13]]]
 hmul := by decide
 f := ![![![![26078370524988758, -202489133947011116, -10184925432499348], ![105358849636604492, -21247249692901449, 0]], ![![-61015302272401, -535644950241213, 0], ![9367054554389, 3378118904, 0]]]]
 g := ![![![![-288361, 93412, -1215]], ![![2035038, -702640, 49326]]], ![![![1090419, -275108, -68749]], ![![-9608862, 2672150, 373113]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-326123217671383494686940514035937650746946079, -13315463598493297040679170854099038248812982, -8507331968687179491316511532852389894950122])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![24, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![24, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![24, 2, 1]]
  ![![2, 0, 0], ![24, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![48, 4, 2]], ![![2, 2, 0], ![144, -7, 5]]]
 hmul := by decide
 f := ![![![![-12, -30, -2], ![16, -3, 0]], ![![1, 0, 0], ![0, 0, 0]]], ![![![-240, 1836, 85], ![-940, 192, 0]], ![![-60, 0, 0], ![1, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![2, 0, 0]]], ![![![-23, 0, -1], ![2, 0, 0]], ![![-12, -7, -1], ![7, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![24, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![1, 1, 0]] ![![4, 0, 0], ![24, 0, 1]]
  ![![4, 0, 0], ![-24, 1, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![8, 0, 0], ![48, 0, 2]], ![![4, 4, 0], ![144, -11, 1]]]
 hmul := by decide
 f := ![![![![-12, -6, -3], ![12, -2, 0]], ![![1, 0, 0], ![0, 0, 0]]], ![![![-78, 270, 109], ![-437, 90, 0]], ![![-42, 0, 0], ![1, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![6, -5, -5], ![-16, 3, 0]]], ![![![-11, 33, 31], ![88, -18, 0]], ![![60, -93, -88], ![-251, 51, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-24, 1, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![24, 2, 1]]
  ![![4, 0, 0], ![-22, 1, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![96, 8, 4]], ![![2, 2, 0], ![144, -7, 5]]]
 hmul := by decide
 f := ![![![![3948, -30893, -1465], ![15981, -3262, 0]], ![![722, 0, -6], ![0, 0, 0]]], ![![![-172572, 1343776, 63692], ![-695104, 141897, 0]], ![![-31403, 0, 261], ![1, 0, 0]]]]
 g := ![![![![6, -87, 5], ![-32, 0, -4]], ![![20, -866, 49], ![-328, 0, -40]]], ![![![5, 22, -1], ![9, 0, 1]], ![![49, -1717, 97], ![-644, 0, -79]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-22, 1, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![1, 1, 0]] ![![4, 0, 0], ![24, 0, 1]]
  ![![4, 0, 0], ![24, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![16, 0, 0], ![96, 0, 4]], ![![4, 4, 0], ![144, -11, 1]]]
 hmul := by decide
 f := ![![![![-18, -3, -2], ![8, -1, 0]], ![![1, 0, 0], ![0, 0, 0]]], ![![![-30, 99, 40], ![-160, 33, 0]], ![![-30, 0, 0], ![1, 0, 0]]]]
 g := ![![![![4, 0, 0], ![0, 0, 0]], ![![0, -1, 0], ![4, 0, 0]]], ![![![-23, 0, -1], ![4, 0, 0]], ![![-18, -5, -2], ![9, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![24, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
