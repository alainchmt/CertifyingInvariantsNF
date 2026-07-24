import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_644799_1.RI3_1_644799_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![763, -71, 26]

def alpha1 := B.equivFun.symm ![56, 5, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![545, -26, -71]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, -1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-2, -1, 1]] ![![5, 0, 0], ![-2, -1, 1]]
  ![![25, 0, 0], ![-12, 4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-10, -5, 5]], ![![-10, -5, 5], ![226, -17, 2]]]
 hmul := by decide
 f := ![![![![795, -123, 63], ![-275, 0, 0]], ![![0, 0, 0], ![-100, 0, 0]]], ![![![-380, 60, -31], ![136, 0, 0]], ![![0, 0, 0], ![48, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![2, -1, 0], ![5, 0, 0]]], ![![![2, -1, 0], ![5, 0, 0]], ![![10, -1, 0], ![2, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![-12, 4, 1]] ![![5, 0, 0], ![-2, -1, 1]]
  ![![125, 0, 0], ![-62, -46, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![-50, -25, 25]], ![![-60, 20, 5], ![-519, -2, -38]]]
 hmul := by decide
 f := ![![![![11528, -4894, -266], ![-3680, 0, 0]], ![![26000, 0, 0], ![125, 0, 0]]], ![![![-5716, 2428, 131], ![1830, 0, 0]], ![![-12896, 0, 0], ![-62, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![12, 9, 0], ![25, 0, 0]]], ![![![2, 2, 0], ![5, 0, 0]], ![![39, 32, -1], ![87, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![125, 0, 0], ![-62, -46, 1]] ![![5, 0, 0], ![-2, -1, 1]]
  ![![625, 0, 0], ![-187, -171, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![625, 0, 0], ![-250, -125, 125]], ![![-310, -230, 5], ![7231, -2, 212]]]
 hmul := by decide
 f := ![![![![2973733, 2340146, 263944], ![-1604730, 0, 0]], ![![7231250, 0, 0], ![-2500, 0, 0]]], ![![![-889739, -700171, -78973], ![480140, 0, 0]], ![![-2163590, 0, 0], ![748, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![37, 34, 0], ![125, 0, 0]]], ![![![1, 1, 0], ![5, 0, 0]], ![![75, 58, 0], ![212, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![625, 0, 0], ![-187, -171, 1]] ![![5, 0, 0], ![-2, -1, 1]]
  ![![3125, 0, 0], ![-812, 1079, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![3125, 0, 0], ![-1250, -625, 625]], ![![-935, -855, 5], ![26606, -2, 837]]]
 hmul := by decide
 f := ![![![![32398047, 32641678, 3546162], ![-18778320, 0, 0]], ![![133031250, 0, 0], ![-12500, 0, 0]]], ![![![-8418308, -8481613, -921435], ![4879360, 0, 0]], ![![-34566840, 0, 0], ![3248, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![162, -216, 0], ![625, 0, 0]]], ![![![1, -2, 0], ![5, 0, 0]], ![![226, -289, 0], ![837, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![3125, 0, 0], ![-812, 1079, 1]] ![![5, 0, 0], ![-2, -1, 1]]
  ![![763, -71, 26]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![15625, 0, 0], ![-6250, -3125, 3125]], ![![-4060, 5395, 5], ![-163394, 1873, -7288]]]
 hmul := by decide
 f := ![![![![787128495, -1111221354, 16835058], ![-89240115, 0, 0]], ![![3166627779, 0, 0], ![763, 0, 0]]]]
 g := ![![![![19, 2, 1]], ![![-55, -7, 1]]], ![![![-61, 5, 7]], ![![-32, -12, -21]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![-2, 1, 0]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![56, 5, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-22, 11, 0]], ![![-22, 11, 0], ![1, -6, 9]]]
 hmul := by decide
 f := ![![![![-1785014, -2337177, 5295816], ![112078, -6619770, 0]], ![![0, 0, 0], ![1621676, 1170, 0]]]]
 g := ![![![![3041, -355, 225]], ![![-3647, 426, -270]]], ![![![-3647, 426, -270]], ![![4376, -511, 324]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![661511, -77247, 48968])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![-2, -1, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![55, 0, 0], ![3, 4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![55, 0, 0], ![-10, 5, 0]], ![![-22, -11, 11], ![-149, 3, -8]]]
 hmul := by decide
 f := ![![![![-281, -420, 968], ![22, -1210, 0]], ![![110, 0, 0], ![0, 0, 0]]], ![![![-14, -23, 52], ![7, -65, 0]], ![![6, 0, 0], ![0, 0, 0]]]]
 g := ![![![![4957, 96, -1160], ![308, 1628, 0]], ![![-904, -21, 210], ![-6, -296, 0]]], ![![![-2011, -41, 470], ![-99, -660, 0]], ![![-13418, -271, 3135], ![-677, -4404, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![55, 0, 0], ![3, 4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![-12, 4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![-12, 4, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![275, 0, 0], ![113, 4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![275, 0, 0], ![-50, 25, 0]], ![![-132, 44, 11], ![-144, -27, 37]]]
 hmul := by decide
 f := ![![![![-252, -1837, 3388], ![-121, -4235, 0]], ![![1925, 0, 0], ![0, 0, 0]]], ![![![-103, -755, 1392], ![-47, -1740, 0]], ![![791, 0, 0], ![0, 0, 0]]]]
 g := ![![![![318349, -235668, -86490], ![127116, 606606, 0]], ![![-57933, 42847, 15725], ![-22987, -110292, 0]]], ![![![-152912, 113166, 41532], ![-60940, -291291, 0]], ![![-167030, 123557, 45346], ![-66358, -318045, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![275, 0, 0], ![113, 4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![125, 0, 0], ![-62, -46, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![125, 0, 0], ![-62, -46, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![1375, 0, 0], ![-312, 79, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![1375, 0, 0], ![-250, 125, 0]], ![![-682, -506, 11], ![106, 123, -413]]]
 hmul := by decide
 f := ![![![![28794, 16640, 27588], ![-3718, -34485, 0]], ![![78375, 0, 0], ![0, 0, 0]]], ![![![-6533, -3776, -6260], ![847, 7825, 0]], ![![-17784, 0, 0], ![0, 0, 0]]]]
 g := ![![![![13438, 16541, -25046], ![-1540, 48235, 0]], ![![-2188, -3072, 4553], ![1405, -8770, 0]]], ![![![-6337, -8288, 12422], ![2211, -23925, 0]], ![![1135, 1257, -1940], ![297, 3735, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1375, 0, 0], ![-312, 79, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![625, 0, 0], ![-187, -171, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![625, 0, 0], ![-187, -171, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![6875, 0, 0], ![1688, 454, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![6875, 0, 0], ![-1250, 625, 0]], ![![-2057, -1881, 11], ![731, 498, -1538]]]
 hmul := by decide
 f := ![![![![338213, 305368, 88088], ![-33726, -110110, 0]], ![![1251250, 0, 0], ![0, 0, 0]]], ![![![83041, 74976, 21628], ![-8278, -27035, 0]], ![![307216, 0, 0], ![0, 0, 0]]]]
 g := ![![![![16871, -10459, -51562], ![9251, 86691, 0]], ![![-4602, 1489, 9374], ![4568, -15762, 0]]], ![![![-5695, 2955, 15427], ![-132, -25938, 0]], ![![1899, -1085, -5487], ![562, 9225, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6875, 0, 0], ![1688, 454, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3125, 0, 0], ![-812, 1079, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![3125, 0, 0], ![-812, 1079, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![34375, 0, 0], ![-13312, 1079, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![34375, 0, 0], ![-6250, 3125, 0]], ![![-8932, 11869, 11], ![-1769, -5127, 9712]]]
 hmul := by decide
 f := ![![![![11881011, -16974781, 693088], ![-3703337, -866360, 0]], ![![49225000, 0, 0], ![0, 0, 0]]], ![![![-4601017, 6573622, -268404], ![1434157, 335505, 0]], ![![-19062784, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1074753525, 5346412721, -3352458125], ![-248485501, 11863392684, 0]], ![![-195397630, -972076021, 609537840], ![45210432, -2156980488, 0]]], ![![![-279258768, -1389212357, 871102753], ![64579900, -3082584076, 0]], ![![-55310043, -275184942, 172553777], ![12811457, -610618580, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![34375, 0, 0], ![-13312, 1079, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
