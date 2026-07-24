import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_420812_2.RI3_1_420812_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-4, 1, -2]

def alpha1 := B.equivFun.symm ![2, 0, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![0, 1, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![25, 0, 0], ![8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-10, 5, 0], ![5, -4, 2]]]
 hmul := by decide
 f := ![![![![270789, -697382, 748904], ![-247790, -1878000, 0]], ![![0, 0, 0], ![28400, -100, 0]]], ![![![86616, -223065, 239544], ![-79254, -600696, 0]], ![![0, 0, 0], ![9084, -32, 0]]]]
 g := ![![![![-165, -1580, -396], ![-100, 4950, 0]], ![![63, 646, 162], ![55, -2025, 0]]], ![![![63, 646, 162], ![55, -2025, 0]], ![![-37, -328, -82], ![-12, 1026, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![8, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![125, 0, 0], ![33, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![-50, 25, 0]], ![![40, 5, 0], ![-15, 6, 2]]]
 hmul := by decide
 f := ![![![![38192284701, -97784738413, 104710160304], ![-34833861560, -261781747500, 0]], ![![716481625, 31698000, 0], ![182000, -500, 0]]], ![![![10081924563, -25813023853, 27641183168], ![-9195374591, -69104633320, 0]], ![![189135417, 8367576, 0], ![48044, -132, 0]]]]
 g := ![![![![-6857, -258954, -15696], ![-3750, 981000, 0]], ![![2725, 104300, 6322], ![1650, -395125, 0]]], ![![![-2211, -82722, -5014], ![-1120, 313375, 0]], ![![822, 31247, 1894], ![473, -118374, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![125, 0, 0], ![33, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![625, 0, 0], ![-217, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![625, 0, 0], ![-250, 125, 0]], ![![165, 5, 0], ![-65, 31, 2]]]
 hmul := by decide
 f := ![![![![-28701091486374, 73159996716312, -78367940091696], ![26112435937815, 195921763830000, 0]], ![![-143575891875, -47840285000, 0], ![1410000, -2500, 0]]], ![![![9965100317740, -25401358233002, 27209570934928], ![-9066311773696, -68024591744928, 0]], ![![49849956627, 16610282556, 0], ![-489556, 868, 0]]]]
 g := ![![![![-20205, 5608990, -51696], ![16250, 16155000, 0]], ![![8284, -2259177, 20822], ![-6125, -6506875, 0]]], ![![![-5300, 1480150, -13642], ![4380, 4263125, 0]], ![![2141, -587199, 5412], ![-1627, -1691249, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![625, 0, 0], ![-217, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![3125, 0, 0], ![-217, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![3125, 0, 0], ![-1250, 625, 0]], ![![-1085, 5, 0], ![435, -219, 2]]]
 hmul := by decide
 f := ![![![![-103575034605580625, 263696602757041875, -282530612502210446], ![94169334393640625, 706326532162625000, 0]], ![![64913271637500, -113387000000, 0], ![-1121875, 3125, 0]]], ![![![7192342597187258, -18311326816982307, 19619177218209372], ![-6539202402271361, -49047943108513184, 0]], ![![-4507635363088, 7873694208, 0], ![77904, -217, 0]]]]
 g := ![![![![-69979, 15374012, -141696], ![12500, 221400000, 0]], ![![28362, -6192311, 57072], ![-2500, -89175000, 0]]], ![![![24383, -5338199, 49200], ![-3120, -76875000, 0]], ![![-9714, 2155026, -19862], ![3123, 31034376, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![3125, 0, 0], ![-217, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![-4, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![15625, 0, 0], ![-6250, 3125, 0]], ![![-1085, 5, 0], ![435, -219, 2]]]
 hmul := by decide
 f := ![![![![126339428017611478, -321603748595589272, 344575076349185340], ![-114856520926162443, -861437690831440296, 0]], ![![-79230796603901, -25951909212, 0], ![1437, -4, 0]]]]
 g := ![![![![-5256, 73, -144]], ![![2117, 14, 58]]], ![![![365, -5, 10]], ![![-147, -1, -4]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![26, 0, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![2, 0, 0], ![26, 0, 1]] ![![2, 0, 0], ![26, 0, 1]]
  ![![2, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![52, 0, 2]], ![![52, 0, 2], ![657, -19, 14]]]
 hmul := by decide
 f := ![![![![-124963, 7497058, 4441945], ![596751, 0, 789600]], ![![0, 0, 0], ![-800, 0, 3]]], ![![![-170, 9372, 5552], ![747, 0, 987]], ![![0, 0, 0], ![-1, 0, 0]]]]
 g := ![![![![1, -1, 0], ![2, 0, 0]], ![![21, -5, 1], ![10, 0, 0]]], ![![![21, -5, 1], ![10, 0, 0]], ![![275, -63, 7], ![107, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![26, 0, 1]]
  ![![2, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![4, 0, 0], ![52, 0, 2]], ![![2, 2, 0], ![26, -12, 2]]]
 hmul := by decide
 f := ![![![![-23, 1131, 676], ![91, 0, 120]], ![![0, 0, 0], ![-3, 0, 0]]]]
 g := ![![![![2, 0, 0]], ![![26, 0, 1]]], ![![![1, 1, 0]], ![![13, -6, 1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-76, 1, -2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![26, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![-2, 1, 0]] ![![2, 0, 0], ![26, 0, 1]]
  ![![10, 0, 0], ![26, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![130, 0, 5]], ![![-4, 2, 0], ![-52, -12, -1]]]
 hmul := by decide
 f := ![![![![342, -20470, -12139], ![-1614, 0, -2160]], ![![-320, -35, 0], ![0, 0, 0]]], ![![![871, -53222, -31562], ![-4195, 0, -5616]], ![![-832, -91, 0], ![0, 0, 0]]]]
 g := ![![![![-19, 1045, -75], ![15, 855, 10]], ![![52, 13585, -963], ![80, 11115, 130]]], ![![![-21, -407, 28], ![5, -333, -4]], ![![-39, -5500, 390], ![-25, -4500, -52]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![26, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![5, 0, 0], ![-2, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![10, 0, 0], ![3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![10, 0, 0], ![5, 5, 0]], ![![-4, 2, 0], ![-1, -1, 2]]]
 hmul := by decide
 f := ![![![![-109, 61, 14], ![-22, 0, 0]], ![![-320, -35, 0], ![0, 0, 0]]], ![![![-32, 17, 4], ![-5, 0, 0]], ![![-92, -10, 0], ![0, 0, 0]]]]
 g := ![![![![-24, -83, -56], ![-10, 280, 0]], ![![-10, -35, -24], ![-5, 120, 0]]], ![![![8, 35, 24], ![12, -120, 0]], ![![-1, 6, 5], ![11, -24, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![8, 1, 0]] ![![2, 0, 0], ![26, 0, 1]]
  ![![50, 0, 0], ![6, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![50, 0, 0], ![650, 0, 25]], ![![16, 2, 0], ![208, -12, 9]]]
 hmul := by decide
 f := ![![![![5265460, -314146400, -186090336], ![-24594020, 0, -33065200]], ![![1060400, -48175, 0], ![0, 0, 0]]], ![![![631837, -37697568, -22330841], ![-2951281, 0, -3967824]], ![![127248, -5781, 0], ![0, 0, 0]]]]
 g := ![![![![17, -3325, 136], ![25, -5225, 50]], ![![248, -43225, 1773], ![100, -67925, 650]]], ![![![1, -1071, 43], ![45, -1683, 16]], ![![79, -13790, 566], ![35, -21670, 208]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![6, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![25, 0, 0], ![8, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![50, 0, 0], ![-17, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![50, 0, 0], ![25, 25, 0]], ![![16, 2, 0], ![9, 9, 2]]]
 hmul := by decide
 f := ![![![![-276667, 33733, 3854], ![-121466, 0, 0]], ![![1060400, -48175, 0], ![0, 0, 0]]], ![![![94184, -11484, -1312], ![41351, 0, 0]], ![![-360987, 16400, 0], ![0, 0, 0]]]]
 g := ![![![![140, -2795, 329], ![-75, -8225, 0]], ![![81, -1368, 161], ![0, -4025, 0]]], ![![![45, -892, 105], ![-23, -2625, 0]], ![![38, -493, 58], ![26, -1449, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![-17, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![125, 0, 0], ![33, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![125, 0, 0], ![33, 1, 0]] ![![2, 0, 0], ![26, 0, 1]]
  ![![250, 0, 0], ![-44, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![250, 0, 0], ![3250, 0, 125]], ![![66, 2, 0], ![858, -12, 34]]]
 hmul := by decide
 f := ![![![![594099480, -35427625125, -20989523966], ![-2771468460, 0, -3729210750]], ![![28377000, -394000, 0], ![0, 0, 0]]], ![![![-104561535, 6235262022, 3694156217], ![487778451, 0, 656341092]], ![![-4994352, 69344, 0], ![0, 0, 0]]]]
 g := ![![![![42, -47500, 661], ![125, -144875, 250]], ![![260, -617500, 8600], ![0, -1883375, 3250]]], ![![![44, -12560, 174], ![220, -38308, 66]], ![![110, -162900, 2268], ![235, -496845, 858]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![250, 0, 0], ![-44, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![125, 0, 0], ![33, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![250, 0, 0], ![33, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![250, 0, 0], ![125, 125, 0]], ![![66, 2, 0], ![34, 34, 2]]]
 hmul := by decide
 f := ![![![![-6219813, 1145562, 6304], ![-2537124, 0, 0]], ![![28377000, -394000, 0], ![0, 0, 0]]], ![![![-820889, 151191, 832], ![-334849, 0, 0]], ![![3745188, -52000, 0], ![0, 0, 0]]]]
 g := ![![![![-20746, -708587, -42946], ![-5500, 5368250, 0]], ![![-10335, -352495, -21364], ![-2625, 2670500, 0]]], ![![![-5503, -187039, -11336], ![-1248, 1417000, 0]], ![![-2823, -95879, -5811], ![-624, 726376, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![250, 0, 0], ![33, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![625, 0, 0], ![-217, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![625, 0, 0], ![-217, 1, 0]] ![![2, 0, 0], ![26, 0, 1]]
  ![![1250, 0, 0], ![206, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![1250, 0, 0], ![16250, 0, 625]], ![![-434, 2, 0], ![-5642, -12, -216]]]
 hmul := by decide
 f := ![![![![18861973510194, -1124698337163125, -666350985494477], ![-87969837114438, 0, -118389317403750]], ![![-136502958750, -115876250, 0], ![0, 0, 0]]], ![![![3108453234475, -185350285964483, -109814642409490], ![-14497429156459, 0, -19510559508138]], ![![-22495687602, -19096406, 0], ![0, 0, 0]]]]
 g := ![![![![20, -1698125, -10276], ![0, 12635000, 1250]], ![![157, -22075625, -133588], ![625, 164255000, 16250]]], ![![![-208, 589446, 3566], ![1220, -4385808, -434]], ![![-232, 7665515, 46386], ![860, -57035720, -5642]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1250, 0, 0], ![206, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![625, 0, 0], ![-217, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![1250, 0, 0], ![-217, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1250, 0, 0], ![625, 625, 0]], ![![-434, 2, 0], ![-216, -216, 2]]]
 hmul := by decide
 f := ![![![![-39524396980, 8047417395, 370804], ![-15738489790, 0, 0]], ![![-136502958750, -115876250, 0], ![0, 0, 0]]], ![![![6861480680, -1397040897, -64372], ![2732219893, 0, 0]], ![![23697070313, 20116250, 0], ![0, 0, 0]]]]
 g := ![![![![-30348, 7033069, -64821], ![11875, 40513125, 0]], ![![-15205, 3511490, -32364], ![5625, 20227500, 0]]], ![![![10602, -2441898, 22506], ![-3748, -14066250, 0]], ![![5267, -1213571, 11185], ![-1874, -6990624, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1250, 0, 0], ![-217, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3125, 0, 0], ![-217, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![3125, 0, 0], ![-217, 1, 0]] ![![2, 0, 0], ![26, 0, 1]]
  ![![6250, 0, 0], ![1456, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![6250, 0, 0], ![81250, 0, 3125]], ![![-434, 2, 0], ![-5642, -12, -216]]]
 hmul := by decide
 f := ![![![![44941997987117712, -2679754075304778125, -1587679446681965534], ![-209593749508452324, 0, -282079386911643750]], ![![-325028499168750, -52610631250, 0], ![0, 0, 0]]], ![![![10469687851078937, -624275509383001112, -369865803899030691], ![-48826959885489053, 0, -65713213974936528]], ![![-75718639166352, -12256172656, 0], ![0, 0, 0]]]]
 g := ![![![![-708, -73268750, -53089], ![3125, 322940625, 6250]], ![![260, -952493750, -690150], ![0, 4198228125, 81250]]], ![![![-868, 5086548, 3685], ![3720, -22419558, -434]], ![![-364, 66148570, 47929], ![1485, -291557595, -5642]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6250, 0, 0], ![1456, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![3125, 0, 0], ![-217, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![6250, 0, 0], ![-217, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![6250, 0, 0], ![3125, 3125, 0]], ![![-434, 2, 0], ![-216, -216, 2]]]
 hmul := by decide
 f := ![![![![-75300111047920, -120394585185389, 47513125439930], ![195740111037252, -45139890622944, -2373201146182]], ![![-254553125, -52610631250, 0], ![0, 0, 0]]], ![![![2614423624120, 4180106022967, -1649658093161], ![-6796106451264, 1567259261541, 82397662568]], ![![8839063, 1826643750, 0], ![0, 0, 0]]]]
 g := ![![![![-8121521, 1766631738, -16282321], ![565625, 50882253125, 0]], ![![-4059433, 883039574, -8138614], ![284375, 25433168750, 0]]], ![![![564021, -122675085, 1130646], ![-37498, -3533268750, 0]], ![![280728, -61035696, 562541], ![-15624, -1757940624, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6250, 0, 0], ![-217, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl
