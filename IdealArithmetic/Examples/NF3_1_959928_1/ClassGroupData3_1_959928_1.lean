import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_959928_1.RI3_1_959928_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-10052, -3035, -498]

def alpha1 := B.equivFun.symm ![168490, 50874, 8348]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![17310155412316, 3449422268493, -870488787881]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-27, -2, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![10, 0, 0], ![-27, -2, 1]] ![![10, 0, 0], ![-27, -2, 1]]
  ![![50, 0, 0], ![8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![100, 0, 0], ![-270, -20, 10]], ![![-270, -20, 10], ![-378, 43, 2]]]
 hmul := by decide
 f := ![![![![71326757135265596, 7156159383132380, 9669698054704067], ![-193046506336373174, -24087327745461820, 0]], ![![0, 0, 0], ![1074510832255, -11009445, 0]]], ![![![10461214961820911, 1049565753648794, 1418216585598090], ![-28313371889086367, -3532793632034096, 0]], ![![0, 0, 0], ![157594278031, -1614712, 0]]]]
 g := ![![![![-6, 2393, 532], ![50, -13300, 0]], ![![9, -6412, -1425], ![-90, 35630, 0]]], ![![![9, -6412, -1425], ![-90, 35630, 0]], ![![15, -9154, -2035], ![-141, 50876, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![50, 0, 0], ![8, 1, 0]] ![![10, 0, 0], ![-27, -2, 1]]
  ![![500, 0, 0], ![-142, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![500, 0, 0], ![-1350, -100, 50]], ![![80, 10, 0], ![30, 3, 4]]]
 hmul := by decide
 f := ![![![![-1551742506521, -155702111446, -210367544186], ![4199808435520, 524032824000, 0]], ![![111036000, -4401500, 0], ![787500, -500, 0]]], ![![![440680784809, 44217986154, 59742472786], ![-1192707468908, -148820564732, 0]], ![![-31533216, 1249986, 0], ![-223643, 142, 0]]]]
 g := ![![![![1350, 2513950, -35659], ![4750, 8914750, 0]], ![![-3503, -6781716, 96195], ![-12325, -24048725, 0]]], ![![![216, 401637, -5697], ![760, 1424250, 0]], ![![152, 150658, -2137], ![535, 534252, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![500, 0, 0], ![-142, 1, 0]] ![![10, 0, 0], ![-27, -2, 1]]
  ![![-10052, -3035, -498]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![5000, 0, 0], ![-13500, -1000, 500]], ![![-1420, 10, 0], ![4080, 303, -146]]]
 hmul := by decide
 f := ![![![![80791592703742771744829818144, 8106632362230478231140100684, 10952797479234679238893277232], ![-218663347024628111433379201390, -27283843035345316062008389980, 0]], ![![320425161672675926578765, 2272519408423714367950, 0], ![2469727509867105, -313616191728, 0]]]]
 g := ![![![![11492, 1664, -466]], ![![38565, -395, -495]]], ![![![-3493, -491, 139]], ![![-11196, 141, 139]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow4 : J0 ^ 4 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-31, -1, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![2, 0, 0], ![-31, -1, 1]] ![![2, 0, 0], ![-31, -1, 1]]
  ![![168490, 50874, 8348]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-62, -2, 2]], ![![-62, -2, 2], ![346, 90, -12]]]
 hmul := by decide
 f := ![![![![-67501, 4743703, -44744], ![-1347616, 0, 0]], ![![0, 0, 0], ![-240213, 0, 0]]]]
 g := ![![![![-74, -117, 22]], ![![-17303, -74, 267]]], ![![![-17303, -74, 267]], ![![209833, 18072, -6308]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![110926734358129508314683802, 33493304218346072862870015, 5495972553366110487890099])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-31, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-27, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![10, 0, 0], ![-27, -2, 1]] ![![2, 0, 0], ![-31, -1, 1]]
  ![![10, 0, 0], ![-4, 2, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![20, 0, 0], ![-310, -10, 10]], ![![-54, -4, 2], ![-24, 70, -6]]]
 hmul := by decide
 f := ![![![![-27354702, -433707961, 50339845], ![666022193, 0, 0]], ![![-3833445672, 16064, 0], ![-171, 0, 0]]], ![![![6072397, 96277508, -11174789], ![-147848235, 0, 0]], ![![850974915, -3566, 0], ![38, 0, 0]]]]
 g := ![![![![2, 4, -8], ![0, 20, 0]], ![![-31, -62, 123], ![0, -305, 0]]], ![![![-5, -11, 21], ![1, -52, 0]], ![![-2, -5, 23], ![1, -59, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-4, 2, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![50, 0, 0], ![8, 1, 0]] ![![2, 0, 0], ![-31, -1, 1]]
  ![![100, 0, 0], ![-54, -4, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![100, 0, 0], ![-1550, -50, 50]], ![![16, 2, 0], ![-2, 8, 6]]]
 hmul := by decide
 f := ![![![![-14186, -584056, -203503], ![410438, 0, 0]], ![![39849850, -42900, 0], ![0, 0, 0]]], ![![![7663, 314376, 109537], ![-220921, 0, 0]], ![![-21449619, 23088, 0], ![0, 0, 0]]]]
 g := ![![![![430228, 33628, -4373], ![-233750, -113100, 0]], ![![-6660209, -520584, 67696], ![3618725, 1750875, 0]]], ![![![68524, 5356, -697], ![-37186, -18009, 0]], ![![-9902, -774, 100], ![5443, 2610, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100, 0, 0], ![-54, -4, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![500, 0, 0], ![-142, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![500, 0, 0], ![-142, 1, 0]] ![![2, 0, 0], ![-31, -1, 1]]
  ![![500, 0, 0], ![216, 2, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![1000, 0, 0], ![-15500, -500, 500]], ![![-284, 2, 0], ![4648, 158, -144]]]
 hmul := by decide
 f := ![![![![62198632320, -449581741587, 296727116911], ![-590924371499, 0, 0]], ![![32470160747398, -316238508651, 0], ![-158841, 0, 0]]], ![![![26991859225, -195101509829, 128768371044], ![-256438877310, 0, 0]], ![![14090824426544, -137235578766, 0], ![-68931, 0, 0]]]]
 g := ![![![![-322, 187041, 3432], ![750, -429000, 0]], ![![4181, -2894893, -53117], ![-9750, 6639750, 0]]], ![![![53, -53137, -975], ![-124, 121875, 0]], ![![-1342, 868025, 15927], ![3128, -1990911, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![500, 0, 0], ![216, 2, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
