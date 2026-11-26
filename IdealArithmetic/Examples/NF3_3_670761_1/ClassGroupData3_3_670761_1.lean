import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_670761_1.RI3_3_670761_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![6, 2, -1]

def alpha1 := B.equivFun.symm ![-101, -4, 5]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![50, 1, -2]

def zeta2 := B.equivFun.symm ![-1, -2, 1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-19, -6, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![11, 0, 0], ![-19, -6, 1]] ![![11, 0, 0], ![-19, -6, 1]]
  ![![121, 0, 0], ![-109, -7, 9]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-209, -66, 11]], ![![-209, -66, 11], ![104, -217, 326]]]
 hmul := by decide
 f := ![![![![47000787766, 859749077499, -2209142683131], ![-750968374112, -410697032350, 0]], ![![0, 0, 0], ![-33116732, -5445, 0]]], ![![![-41795745799, -764537268807, 1964494010615], ![667803344888, 365214916352, 0]], ![![0, 0, 0], ![29449262, 4842, 0]]]]
 g := ![![![![55897, 163968, -35676], ![-62436, -152460, 0]], ![![-96062, -281937, 61340], ![107415, 262152, 0]]], ![![![-96062, -281937, 61340], ![107415, 262152, 0]], ![![49488, 145131, -31576], ![-55250, -134946, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![121, 0, 0], ![-109, -7, 9]] ![![11, 0, 0], ![-19, -6, 1]]
  ![![6, 2, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![1331, 0, 0], ![-2299, -726, 121]], ![![-1199, -77, 99], ![1450, -727, 129]]]
 hmul := by decide
 f := ![![![![75331642428987105, 1378784268357367144, -3542711749483033812], ![-1204247142343453747, -658591338648261088, 0]], ![![5557990708018, -62448001434, 0], ![-899472, -34, 0]]]]
 g := ![![![![271, 11, -7]], ![![-406, -33, -23]]], ![![![-231, 0, 11]], ![![358, -1, -42]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-6, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![17, 0, 0], ![-6, 1, 0]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![289, 0, 0], ![96, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![289, 0, 0], ![-102, 17, 0]], ![![-102, 17, 0], ![31, -17, 11]]]
 hmul := by decide
 f := ![![![![25467, 60058, -59774], ![-5440, 92480, 0]], ![![0, 0, 0], ![-1734, 0, 0]]], ![![![101507, 239422, -238282], ![-21724, 368656, 0]], ![![0, 0, 0], ![-6918, -7, 0]]]]
 g := ![![![![24963, -494517, -59774], ![6647, 1570426, 0]], ![![-8833, 174637, 21109], ![-2295, -554591, 0]]], ![![![-8833, 174637, 21109], ![-2295, -554591, 0]], ![![2668, -53147, -6424], ![759, 168777, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![289, 0, 0], ![96, 1, 0]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![-101, -4, 5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![4913, 0, 0], ![-1734, 289, 0]], ![![1632, 17, 0], ![-581, 85, 11]]]
 hmul := by decide
 f := ![![![![-101923667638, -240708436012, 239471530998], ![21813739401, -370083316550, 0]], ![![2323800618, -153832574, 0], ![-159071, -40, 0]]]]
 g := ![![![![-57, -109, -94]], ![![19, -60, -65]]], ![![![-19, -42, -37]], ![![6, -24, -25]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![0, -1, -1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-51, -1, 2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![17, 0, 0], ![-6, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![289, 0, 0], ![96, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-19, -6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![11, 0, 0], ![-19, -6, 1]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![187, 0, 0], ![317, 5, -20]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![187, 0, 0], ![-66, 11, 0]], ![![-323, -102, 17], ![150, 70, -67]]]
 hmul := by decide
 f := ![![![![9124490121, 21569904028, -21436397369], ![-1951590378, 33123117016, 0]], ![![41201336, -8415, 0], ![0, 0, 0]]], ![![![15440611713, 36500945091, -36275022934], ![-3302513234, 56051481446, 0]], ![![69721576, -14240, 0], ![0, 0, 0]]]]
 g := ![![![![84306, 371201, 115540], ![141185, 417384, 0]], ![![-30172, -131623, -40950], ![-49896, -147994, 0]]], ![![![-145125, -635554, -197769], ![-241264, -714612, 0]], ![![66723, 293895, 91479], ![111797, 330460, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![187, 0, 0], ![317, 5, -20]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![11, 0, 0], ![-19, -6, 1]] ![![289, 0, 0], ![96, 1, 0]]
  ![![3179, 0, 0], ![10595, 333, -637]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3179, 0, 0], ![1056, 11, 0]], ![![-5491, -1734, 289], ![-1788, -542, 35]]]
 hmul := by decide
 f := ![![![![641564791781250, -12699350823735120, -1535017940097149], ![169172557741524, 40329072109137306, 0]], ![![14883458095, -286110, 0], ![0, 0, 0]]], ![![![2130745862528445, -42176705410130730, -5098055826423835], ![561850856029860, 133939712149059513, 0]], ![![49430497375, -950220, 0], ![0, 0, 0]]]]
 g := ![![![![207280541, 4058616516, -120624624], ![1140141992, 2321623700, 0]], ![![68843494, 1348158451, -40067563], ![378726029, 771178375, 0]]], ![![![-357775984, -7005260283, 208201034], ![-1967908219, -4007172850, 0]], ![![-116506842, -2281145476, 67797357], ![-640815336, -1304868550, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3179, 0, 0], ![10595, 333, -637]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![-109, -7, 9]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![121, 0, 0], ![-109, -7, 9]] ![![17, 0, 0], ![-6, 1, 0]]
  ![![2057, 0, 0], ![15119, 1423, -830]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![2057, 0, 0], ![-726, 121, 0]], ![![-1853, -119, 153], ![743, 175, -86]]]
 hmul := by decide
 f := ![![![![51991441599572, 122822973986522, -122175862822433], ![-11125039741803, 188766402033286, 0]], ![![442249518095, -8351420, 0], ![0, 0, 0]]], ![![![381624547390218, 901538030388389, -896788142762481], ![-81659367879571, 1385572134992148, 0]], ![![3246174119895, -61300606, 0], ![0, 0, 0]]]]
 g := ![![![![-420970241, 3260669943, -3572915811], ![603221421, 682444719, 0]], ![![148578268, -1150937570, 1261152135], ![-212920433, -240886195, 0]]], ![![![379200857, -2937188557, 3218457145], ![-543376678, -614741284, 0]], ![![-152046370, 1177610020, -1290379942], ![217858537, 246469106, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2057, 0, 0], ![15119, 1423, -830]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![121, 0, 0], ![-109, -7, 9]] ![![289, 0, 0], ![96, 1, 0]]
  ![![34969, 0, 0], ![-62729, -17127, 3374]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![34969, 0, 0], ![11616, 121, 0]], ![![-31501, -2023, 2601], ![-10375, -539, 832]]]
 hmul := by decide
 f := ![![![![3259637590702404353, -64522404943854589707, -7799063864454553616], ![859525272538326253, 204902394787417813453, 0]], ![![144872424187601, -95465370, 0], ![0, 0, 0]]], ![![![-5824480718710482022, 115291805626566437343, 13935750781644003078], ![-1535842018580068427, -366129673759145451278, 0]], ![![-258865170704974, 170582217, 0], ![0, 0, 0]]]]
 g := ![![![![1993381068721, 45221581327197, -103584409360251], ![-35718682801593, -21820226825463, 0]], ![![662160989159, 15021696850963, -34408650686417], ![-11865025691486, -7248239067531, 0]]], ![![![-1795686716598, -40736714293750, 93311387324711], ![32176269277655, 19656197775864, 0]], ![![-591417923173, -13416830363339, 30732548685958], ![10597407153888, 6473862113466, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![34969, 0, 0], ![-62729, -17127, 3374]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
