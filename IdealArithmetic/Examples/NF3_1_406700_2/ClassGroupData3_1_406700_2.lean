import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_406700_2.RI3_1_406700_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![45, -2, 2]

def alpha1 := B.equivFun.symm ![-12, 2, -1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![6, 2, -1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![13, 0, 0], ![2, 1, 0]] ![![13, 0, 0], ![2, 1, 0]]
  ![![169, 0, 0], ![-24, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![169, 0, 0], ![26, 13, 0]], ![![26, 13, 0], ![5, 3, 5]]]
 hmul := by decide
 f := ![![![![1026909702, 1045642273, 5321909260], ![238420130, -13839627841, 0]], ![![0, 0, 0], ![34563880, 13013, 0]]], ![![![-146385707, -149056030, -758636760], ![-33986726, 1972835295, 0]], ![![0, 0, 0], ![-4927072, -1855, 0]]]]
 g := ![![![![-234, 6474, -1295], ![169, 43771, 0]], ![![-35, 925, -185], ![13, 6253, 0]]], ![![![-35, 925, -185], ![13, 6253, 0]], ![![-3, 175, -35], ![28, 1184, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![169, 0, 0], ![-24, 1, 0]] ![![13, 0, 0], ![2, 1, 0]]
  ![![45, -2, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![2197, 0, 0], ![338, 169, 0]], ![![-312, 13, 0], ![-47, -23, 5]]]
 hmul := by decide
 f := ![![![![-175138786385137, -178278622507611, -907028066093059], ![-40658168867526, 2358273007964110, 0]], ![![82554475851, -470348894, 0], ![9964216, 3479, 0]]]]
 g := ![![![![17, -6, 14]], ![![-70, -25, 2]]], ![![![-8, -1, -2]], ![![9, 3, -1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![7, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![19, 0, 0], ![7, 1, 0]] ![![19, 0, 0], ![7, 1, 0]]
  ![![361, 0, 0], ![-126, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![361, 0, 0], ![133, 19, 0]], ![![133, 19, 0], ![50, 13, 5]]]
 hmul := by decide
 f := ![![![![-312081818, -2454345582, -2057120055], ![-244153591, 7820675120, 0]], ![![0, 0, 0], ![-69051719, 19494, 0]]], ![![![109022109, 857396766, 718630700], ![85292197, -2732060884, 0]], ![![0, 0, 0], ![24122406, -6810, 0]]]]
 g := ![![![![-20683, 3378915, -133030], ![16967, 9604766, 0]], ![![-7640, 1243186, -48945], ![6156, 3533829, 0]]], ![![![-7640, 1243186, -48945], ![6156, 3533829, 0]], ![![-2871, 466846, -18380], ![2306, 1327037, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![361, 0, 0], ![-126, 1, 0]] ![![19, 0, 0], ![7, 1, 0]]
  ![![-12, 2, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![6859, 0, 0], ![2527, 361, 0]], ![![-2394, 19, 0], ![-881, -120, 5]]]
 hmul := by decide
 f := ![![![![1779219129345802, 13999932578894218, 11727193182611571], ![1392340341279736, -44563356836114192, 0]], ![![-152571242769666, 432101736570, 0], ![-2402496, -660, 0]]]]
 g := ![![![![-350, 5, -26]], ![![-37, 16, -11]]], ![![![127, -1, 9]], ![![15, -5, 4]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-1124, 41, -44])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![19, 0, 0], ![7, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![361, 0, 0], ![-126, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![13, 0, 0], ![2, 1, 0]] ![![19, 0, 0], ![7, 1, 0]]
  ![![247, 0, 0], ![-50, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![247, 0, 0], ![91, 13, 0]], ![![38, 19, 0], ![15, 8, 5]]]
 hmul := by decide
 f := ![![![![-1485244, -11674495, -9793675], ![-1161622, 37238708, 0]], ![![-295906, -15561, 0], ![0, 0, 0]]], ![![![301510, 2370004, 1988185], ![235831, -7559720, 0]], ![![60071, 3159, 0], ![0, 0, 0]]]]
 g := ![![![![-34765, 1928555, -189080], ![15067, 9340552, 0]], ![![-12767, 709897, -69600], ![5694, 3438240, 0]]], ![![![-5296, 295790, -29000], ![2489, 1432600, 0]], ![![-2077, 116735, -11445], ![1047, 565384, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![247, 0, 0], ![-50, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![13, 0, 0], ![2, 1, 0]] ![![361, 0, 0], ![-126, 1, 0]]
  ![![4693, 0, 0], ![1679, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4693, 0, 0], ![-1638, 13, 0]], ![![722, 361, 0], ![-251, -125, 5]]]
 hmul := by decide
 f := ![![![![-60713195458562, 9860549965142920, -388215915196065], ![48505298041446, 28029189084453869, 0]], ![![-1043662191, -262808, 0], ![0, 0, 0]]], ![![![-21719322882985, 3527478118720637, -138878982514580], ![17352113025213, 10027062540163428, 0]], ![![-373356005, -94016, 0], ![0, 0, 0]]]]
 g := ![![![![-1980974, -4298882956, -12809545], ![-1623778, 12023038937, 0]], ![![691023, 1500445665, 4470935], ![567866, -4196419591, 0]]], ![![![-305207, -661241017, -1970325], ![-248368, 1849347045, 0]], ![![105739, 229877591, 684975], ![87364, -642917534, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4693, 0, 0], ![1679, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![-24, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![169, 0, 0], ![-24, 1, 0]] ![![19, 0, 0], ![7, 1, 0]]
  ![![3211, 0, 0], ![-1038, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![3211, 0, 0], ![1183, 169, 0]], ![![-456, 19, 0], ![-167, -18, 5]]]
 hmul := by decide
 f := ![![![![-20510836739, -161400796576, -135183119885], ![-16051402825, 513696075412, 0]], ![![4310292272, -1955499, 0], ![0, 0, 0]]], ![![![6631323075, 52182211806, 43705820195], ![5189551234, -166082187820, 0]], ![![-1393553124, 632229, 0], ![0, 0, 0]]]]
 g := ![![![![4649371, -5957708075, 28670400], ![-3355495, -18412130880, 0]], ![![1712876, -2194836204, 10562255], ![-1236066, -6783080161, 0]]], ![![![-659651, 846077292, -4071595], ![478458, 2614778309, 0]], ![![-240791, 309841174, -1491055], ![177626, 957555522, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3211, 0, 0], ![-1038, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![169, 0, 0], ![-24, 1, 0]] ![![361, 0, 0], ![-126, 1, 0]]
  ![![61009, 0, 0], ![-17093, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![61009, 0, 0], ![-21294, 169, 0]], ![![-8664, 361, 0], ![3025, -151, 5]]]
 hmul := by decide
 f := ![![![![-228858379536249370, 37169259926972698025, -1463376630400335685], ![182840486838061281, 105655792715030126543, 0]], ![![319132283145, -58934694, 0], ![0, 0, 0]]], ![![![64120194977357197, -10413864672602290434, 410000258923073730], ![-51227172409277432, -29602018694281194450, 0]], ![![-89412606435, 16511976, 0], ![0, 0, 0]]]]
 g := ![![![![390015238, -7802654210545, 2282278640], ![-237141983, -27847907509552, 0]], ![![-136121733, 2723364471857, -796584905], ![82789382, 9719769693829, 0]]], ![![![-55369635, 1108070087957, -324110825], ![33738338, 3954735464485, 0]], ![![19338194, -386878177031, 113161980], ![-11757794, -1380779847563, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![61009, 0, 0], ![-17093, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
