import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_603288_2.RI3_1_603288_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-29, 2, -1]

def alpha1 := B.equivFun.symm ![5, -2, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-9, 2, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![15, 1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![15, 1, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![2, 0, 0], ![15, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![30, 2, 2]], ![![30, 2, 2], ![505, 58, 11]]]
 hmul := by decide
 f := ![![![![20889553, 975991841, -375586928], ![456874128, 0, -49117152]], ![![0, 0, 0], ![-73082, 0, -9]]], ![![![153190170, 7157277894, -2754305827], ![3350412325, 0, -360192669]], ![![0, 0, 0], ![-535935, 0, -66]]]]
 g := ![![![![-13, -2, -1], ![2, 0, 0]], ![![0, -1, 0], ![2, 0, 0]]], ![![![0, -1, 0], ![2, 0, 0]], ![![5, -4, -11], ![33, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0], ![15, 2, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![4, 0, 0], ![13, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0], ![30, 2, 2]], ![![30, 4, 2], ![645, 52, 13]]]
 hmul := by decide
 f := ![![![![1516, 70796, -27253], ![33148, 0, -3564]], ![![0, 0, 0], ![-4, 0, 0]]], ![![![4927, 230087, -88572], ![107731, 0, -11583]], ![![0, 0, 0], ![-13, 0, 0]]]]
 g := ![![![![-12, 0, -1], ![4, 0, 0]], ![![1, 53, -6], ![2, 0, -3]]], ![![![1, 106, -12], ![2, 0, -6]], ![![15, 1378, -164], ![45, 0, -78]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0], ![13, 0, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![4, 0, 0], ![13, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0], ![60, 4, 4]], ![![26, 0, 2], ![335, 62, 7]]]
 hmul := by decide
 f := ![![![![602562640, 28248464423, -10865420348], ![13210741892, 0, -1422586333]], ![![-30625056, 0, 0], ![-60764, 0, -7]]], ![![![1807697855, 84745858086, -32596439828], ![39632443050, 0, -4267782407]], ![![-91875672, 0, 0], ![-182293, 0, -21]]]]
 g := ![![![![-11, -2, -1], ![4, 0, 0]], ![![-11, -3, -1], ![8, 0, 0]]], ![![![0, -1, 0], ![2, 0, 0]], ![![-4, 2, -5], ![27, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0], ![13, 2, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![8, 0, 0], ![13, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0], ![60, 4, 4]], ![![26, 4, 2], ![615, 50, 11]]]
 hmul := by decide
 f := ![![![![123740, 5811920, -2234157], ![2716936, 0, -292516]], ![![-7392, 0, 0], ![-8, 0, 0]]], ![![![201065, 9444300, -3630479], ![4414990, 0, -475335]], ![![-12012, 0, 0], ![-13, 0, 0]]]]
 g := ![![![![266, -12, -83], ![440, 0, -28]], ![![1984, -78, -597], ![3156, 0, -203]]], ![![![821, -32, -247], ![1306, 0, -84]], ![![20295, -775, -6068], ![32035, 0, -2065]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![8, 0, 0], ![13, 2, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![8, 0, 0], ![13, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![16, 0, 0], ![120, 8, 8]], ![![26, 4, 2], ![615, 50, 11]]]
 hmul := by decide
 f := ![![![![51904039111, 2440317734902, -938310302731], ![1140284009450, 0, -122845703595]], ![![-2942957248, 0, 0], ![-1365008, 0, -195]]], ![![![83844989186, 3942051863206, -1515732080394], ![1841997310328, 0, -198443066580]], ![![-4754008028, 0, 0], ![-2205013, 0, -315]]]]
 g := ![![![![-11, 2, -1], ![8, 0, 0]], ![![2, 3, 0], ![8, 0, 0]]], ![![![0, 1, 0], ![2, 0, 0]], ![![20, 15, -3], ![35, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![8, 0, 0], ![13, -2, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![16, 0, 0], ![13, 6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![16, 0, 0], ![120, 8, 8]], ![![26, -4, 2], ![55, 74, 3]]]
 hmul := by decide
 f := ![![![![74377, 3491795, -1343250], ![1632130, 0, -175860]], ![![-3136, 0, 0], ![-16, 0, 0]]], ![![![60421, 2836860, -1091305], ![1326002, 0, -142875]], ![![-2548, 0, 0], ![-13, 0, 0]]]]
 g := ![![![![14238, -5076, -811], ![9616, 0, -420]], ![![106277, -37888, -6053], ![71776, 0, -3135]]], ![![![23381, -8344, -1333], ![15810, 0, -690]], ![![44236, -15769, -2520], ![29883, 0, -1305]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![16, 0, 0], ![13, 6, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![16, 0, 0], ![13, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![32, 0, 0], ![240, 16, 16]], ![![26, 12, 2], ![1175, 26, 19]]]
 hmul := by decide
 f := ![![![![11918520040, 561479951794, -215810629902], ![262223561320, 0, -28253797606]], ![![-995277024, 0, 0], ![-564216, 0, -155]]], ![![![9534820260, 449184160544, -172648580451], ![209778942044, 0, -22603048104]], ![![-796221972, 0, 0], ![-451373, 0, -124]]]]
 g := ![![![![-11, 2, -1], ![16, 0, 0]], ![![2, 3, 0], ![16, 0, 0]]], ![![![0, 1, 0], ![2, 0, 0]], ![![32, 8, -2], ![51, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![16, 0, 0], ![13, -2, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![32, 0, 0], ![29, 14, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![32, 0, 0], ![240, 16, 16]], ![![26, -4, 2], ![55, 74, 3]]]
 hmul := by decide
 f := ![![![![65525, 3080583, -1184894], ![1439386, 0, -155124]], ![![-2688, 0, 0], ![-32, 0, 0]]], ![![![59370, 2791240, -1073603], ![1304192, 0, -140554]], ![![-2436, 0, 0], ![-29, 0, 0]]]]
 g := ![![![![13999, -6846, -210], ![9696, 0, -372]], ![![103855, -50760, -1556], ![71880, 0, -2759]]], ![![![11664, -5706, -175], ![8082, 0, -310]], ![![18663, -9127, -280], ![12931, 0, -496]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ08 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![29, 14, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![32, 0, 0], ![29, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := rfl
 M := ![![![64, 0, 0], ![480, 32, 32]], ![![58, 28, 2], ![2535, -6, 51]]]
 hmul := by decide
 f := ![![![![950594067467, 44758172173770, -17209175266848], ![20903953959570, 0, -2252796050043]], ![![-38048247072, 0, 0], ![-1111352, 0, 1323]]], ![![![860061339869, 40495491027463, -15570206931218], ![18913102097238, 0, -2038244141808]], ![![-34424606124, 0, 0], ![-1005509, 0, 1197]]]]
 g := ![![![![-27, 2, -1], ![32, 0, 0]], ![![-14, 3, 0], ![32, 0, 0]]], ![![![0, 1, 0], ![2, 0, 0]], ![![33, 3, 0], ![51, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ09 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![29, -2, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![64, 0, 0], ![29, 30, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![64, 0, 0], ![480, 32, 32]], ![![58, -4, 2], ![295, 90, 19]]]
 hmul := by decide
 f := ![![![![13193384, 620495236, -238655329], ![289870432, 0, -31242708]], ![![-255744, 0, 0], ![-64, 0, 0]]], ![![![5978224, 281160731, -108140245], ![131346992, 0, -14156793]], ![![-115884, 0, 0], ![-29, 0, 0]]]]
 g := ![![![![391051, -116910, -1062], ![122400, 0, -6804]], ![![2929310, -875692, -7953], ![916760, 0, -50967]]], ![![![354832, -106096, -964], ![111090, 0, -6174]], ![![1792323, -535830, -4867], ![560987, 0, -31185]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ010 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![64, 0, 0], ![29, 30, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![64, 0, 0], ![29, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := rfl
 M := ![![![128, 0, 0], ![960, 64, 64]], ![![58, 60, 2], ![4775, -102, 83]]]
 hmul := by decide
 f := ![![![![46381524247767, 2145921563563962, -829390051839302], ![1006127187720666, 0, -108635660995071]], ![![26855182817376, 0, 0], ![-212186584, 0, 14859]]], ![![![21010434062817, 972084127171047, -375706604712781], ![455767016700354, 0, -49211025925224]], ![![12165168285876, 0, 0], ![-96118709, 0, 6731]]]]
 g := ![![![![-27, 2, -1], ![64, 0, 0]], ![![-14, 3, 0], ![64, 0, 0]]], ![![![0, 1, 0], ![2, 0, 0]], ![![37, 1, 0], ![83, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ011 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![64, 0, 0], ![29, -2, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![128, 0, 0], ![29, 62, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010
 hI2 := rfl
 M := ![![![128, 0, 0], ![960, 64, 64]], ![![58, -4, 2], ![295, 90, 19]]]
 hmul := by decide
 f := ![![![![-52128916, -2452334080, 943180955], ![-1145543320, 0, 123474988]], ![![1004032, 0, 0], ![-128, 0, 0]]], ![![![-11810508, -555609383, 213690375], ![-259538300, 0, 27974925]], ![![227476, 0, 0], ![-29, 0, 0]]]]
 g := ![![![![1440110, -298304, -55], ![181792, 0, -21844]], ![![10792443, -2235565, -412], ![1362424, 0, -163703]]], ![![![653071, -135282, -25], ![82450, 0, -9906]], ![![3307205, -685110, -127], ![417595, 0, -50165]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ012 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![128, 0, 0], ![29, 62, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![128, 0, 0], ![29, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ011
 hI2 := rfl
 M := ![![![256, 0, 0], ![1920, 128, 128]], ![![58, 124, 2], ![9255, -294, 147]]]
 hmul := by decide
 f := ![![![![57129465035921984, 2686564327337159375, -1033402086487252876], ![1255052108194368212, 0, -135289332348541905]], ![![1028663577253728, 0, 0], ![-1899739928, 0, 46155]]], ![![![12940928544214772, 608558770288606207, -234085555505642783], ![284293571473092528, 0, -30645649869400185]], ![![233012191535604, 0, 0], ![-430327829, 0, 10455]]]]
 g := ![![![![-27, 2, -1], ![128, 0, 0]], ![![-14, 3, 0], ![128, 0, 0]]], ![![![0, 1, 0], ![2, 0, 0]], ![![68, -2, 1], ![19, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ013 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![128, 0, 0], ![29, -2, 1]] ![![2, 0, 0], ![15, 1, 1]]
  ![![-29, 2, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ012
 hI2 := rfl
 M := ![![![256, 0, 0], ![1920, 128, 128]], ![![58, -4, 2], ![295, 90, 19]]]
 hmul := by decide
 f := ![![![![26177603, 1231658102, -473692983], ![575314638, 0, -62013195]], ![![-502164, 0, 0], ![29, 0, 0]]]]
 g := ![![![![-4, -1, 0]], ![![-100, 1, -3]]], ![![![-2, 0, 0]], ![![-15, -1, -1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow15 : J0 ^ 15 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ013, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![10, 0, 0], ![15, 2, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![10, 0, 0], ![15, 2, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![100, 0, 0], ![45, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![100, 0, 0], ![150, 20, 10]], ![![150, 20, 10], ![785, 46, 17]]]
 hmul := by decide
 f := ![![![![437848943, -180499845, -22941396], ![618379334, -96337456, 0]], ![![0, 0, 0], ![-2126280, -95, 0]]], ![![![175149249, -72203929, -9177066], ![247365408, -38537112, 0]], ![![0, 0, 0], ![-850559, -38, 0]]]]
 g := ![![![![22996, 4542, 687], ![10500, -19800, 0]], ![![33242, 6562, 993], ![15110, -28600, 0]]], ![![![33242, 6562, 993], ![15110, -28600, 0]], ![![177573, 35051, 5304], ![80689, -152768, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![100, 0, 0], ![45, 2, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![5, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1000, 0, 0], ![1500, 200, 100]], ![![450, 20, 10], ![1235, 106, 47]]]
 hmul := by decide
 f := ![![![![-1066555916642970, 440099111567754, 55865253794390], ![-1506227527271447, 234548240856416, 0]], ![![93847197971483, -6662783522, 0], ![-61233527, -990, 0]]]]
 g := ![![![![88, 10, 3]], ![![356, 20, 11]]], ![![![62, 5, 2]], ![![219, 15, 7]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-249, -18, -8])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![15, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100, 0, 0], ![45, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![15, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![15, 1, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![20, 0, 0], ![-5, 4, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![20, 0, 0], ![30, 4, 2]], ![![150, 10, 10], ![645, 52, 13]]]
 hmul := by decide
 f := ![![![![574682, -236719, -29175], ![811772, -126437, 0]], ![![-2808, 0, 0], ![-36, 0, 0]]], ![![![-142500, 58696, 7234], ![-201283, 31351, 0]], ![![696, 0, 0], ![9, 0, 0]]]]
 g := ![![![![596, -44, -43], ![-140, 90, 0]], ![![-68412, 4790, 5041], ![17826, -10386, 6]]], ![![![-168965, 11838, 12448], ![43990, -25650, 15]], ![![-881466, 61757, 64937], ![229479, -133812, 78]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![-5, 4, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![15, 1, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![200, 0, 0], ![45, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![200, 0, 0], ![90, 4, 2]], ![![1500, 100, 100], ![1095, 82, 43]]]
 hmul := by decide
 f := ![![![![985080154681, 194438415130, 29424404996], ![447469082020, -847443504420, 0]], ![![-2711124, 0, 0], ![-360, 0, 0]]], ![![![221641617722, 43748363700, 6620448796], ![100679899820, -190673569432, 0]], ![![-609999, 0, 0], ![-81, 0, 0]]]]
 g := ![![![![289549, 51374, 8479], ![65716, -431955, -1404]], ![![128668, 22832, 3768], ![29298, -191980, -624]]], ![![![2131385, 378170, 62415], ![483840, -3179675, -10335]], ![![1552301, 275422, 45457], ![352327, -2315759, -7527]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![200, 0, 0], ![45, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![15, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![2, 0, 0], ![15, 2, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![20, 0, 0], ![5, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![20, 0, 0], ![30, 4, 2]], ![![150, 20, 10], ![785, 46, 17]]]
 hmul := by decide
 f := ![![![![37082, -15287, -1943], ![52372, -8159, 0]], ![![0, 0, 0], ![-36, 0, 0]]], ![![![9276, -3824, -486], ![13101, -2041, 0]], ![![0, 0, 0], ![-9, 0, 0]]]]
 g := ![![![![591, -88, 10], ![160, -90, 0]], ![![596, -86, 11], ![142, -90, 0]]], ![![![2980, -430, 55], ![710, -450, 0]], ![![19783, -2857, 364], ![4689, -2988, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![5, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![2, 0, 0], ![15, 2, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![200, 0, 0], ![85, 6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![200, 0, 0], ![90, 4, 2]], ![![1500, 200, 100], ![1235, 106, 47]]]
 hmul := by decide
 f := ![![![![106689286, 21058734, 3186753], ![48463320, -91782540, 0]], ![![0, 0, 0], ![-360, 0, 0]]], ![![![45342475, 8949870, 1354356], ![20596716, -39007180, 0]], ![![0, 0, 0], ![-153, 0, 0]]]]
 g := ![![![![566, 324, 61], ![400, -1050, 0]], ![![209, 143, 27], ![290, -474, 0]]], ![![![4680, 2482, 467], ![2100, -7950, 0]], ![![3818, 2036, 383], ![1783, -6528, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![200, 0, 0], ![85, 6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![13, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![4, 0, 0], ![13, 0, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![40, 0, 0], ![5, 2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![40, 0, 0], ![60, 8, 4]], ![![130, 0, 10], ![475, 54, 7]]]
 hmul := by decide
 f := ![![![![12791034, -5198159, -671071], ![18079816, -2835605, 0]], ![![-65056, 0, -6804], ![-72, 0, 0]]], ![![![1603152, -651493, -84115], ![2266036, -355405, 0]], ![![-8132, 0, -854], ![-9, 0, 0]]]]
 g := ![![![![2383, -249, 45], ![292, -635, -28]], ![![2383, -249, 45], ![296, -635, -28]]], ![![![7751, -809, 147], ![934, -2065, -91]], ![![20253, -2113, 383], ![2459, -5395, -238]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![40, 0, 0], ![5, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![4, 0, 0], ![13, 0, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![400, 0, 0], ![-115, 6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![400, 0, 0], ![180, 8, 4]], ![![1300, 0, 100], ![865, 54, 37]]]
 hmul := by decide
 f := ![![![![3056777583994, 603358473564, 91305175381], ![1388530134060, -2629704483500, 0]], ![![-9188964, 0, 0], ![-1520, 0, 0]]], ![![![-878827497491, -173466339248, -26250355671], ![-399204204101, 756043430296, 0]], ![![2641839, 0, 0], ![437, 0, 0]]]]
 g := ![![![![8652897, -9087110, 809712], ![-2621584, -26839980, -6004]], ![![3871018, -4065288, 362240], ![-1172876, -12007368, -2686]]], ![![![28121544, -29533064, 2631565], ![-8521348, -87229860, -19513]], ![![18558061, -19489469, 1736622], ![-5623107, -57564744, -12877]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![400, 0, 0], ![-115, 6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![13, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![4, 0, 0], ![13, 2, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![40, 0, 0], ![5, 6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![40, 0, 0], ![60, 8, 4]], ![![130, 20, 10], ![755, 42, 15]]]
 hmul := by decide
 f := ![![![![10580517, -4338197, -535730], ![14949566, -2333399, 0]], ![![-103360, 0, 0], ![-72, 0, 0]]], ![![![1322570, -542279, -66967], ![1868712, -291677, 0]], ![![-12920, 0, 0], ![-9, 0, 0]]]]
 g := ![![![![671, -93, 56], ![100, -195, 0]], ![![942, -127, 79], ![120, -273, 0]]], ![![![2022, -268, 170], ![230, -585, 0]], ![![12275, -1617, 1032], ![1323, -3549, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![40, 0, 0], ![5, 6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![4, 0, 0], ![13, 2, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![400, 0, 0], ![-35, 14, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![400, 0, 0], ![180, 8, 4]], ![![1300, 200, 100], ![1145, 102, 45]]]
 hmul := by decide
 f := ![![![![430448711, 84963984, 12857238], ![195529860, -370309140, 0]], ![![0, 0, 0], ![-1520, 0, 0]]], ![![![-37665425, -7434577, -1125043], ![-17109372, 32403044, 0]], ![![0, 0, 0], ![133, 0, 0]]]]
 g := ![![![![43751, -17500, 8838], ![-4400, -126100, 0]], ![![19948, -7979, 4024], ![-1724, -57424, 0]]], ![![![148097, -59237, 29913], ![-14700, -426800, 0]], ![![128321, -51327, 25915], ![-12563, -369764, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![400, 0, 0], ![-35, 14, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![13, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![8, 0, 0], ![13, 2, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![80, 0, 0], ![45, 6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![80, 0, 0], ![120, 16, 8]], ![![130, 20, 10], ![755, 42, 15]]]
 hmul := by decide
 f := ![![![![39233722712, -16086306291, -1986555877], ![55434667236, -8652557849, 0]], ![![-767663520, 0, -70260], ![-144, 0, 0]]], ![![![22062690406, -9045972983, -1117119771], ![31173129064, -4865679113, 0]], ![![-431687880, 0, -39510], ![-81, 0, 0]]]]
 g := ![![![![173891, 31512, 18384], ![100440, -130570, -180]], ![![231877, 42020, 24514], ![133920, -174106, -240]]], ![![![246351, 44644, 26046], ![142330, -184990, -255]], ![![1565156, 283629, 165463], ![903823, -1175164, -1620]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![80, 0, 0], ![45, 6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![8, 0, 0], ![13, 2, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![800, 0, 0], ![-35, 14, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![800, 0, 0], ![360, 16, 8]], ![![1300, 200, 100], ![1145, 102, 45]]]
 hmul := by decide
 f := ![![![![425427763966164011, 83973237677788862, 12707323236859162], ![193249031770698260, -365991194190314940, 0]], ![![-1326489983520, 0, -24294564], ![-3040, 0, 0]]], ![![![-18612951921077424, -3673925323966868, -555959945463411], ![-8454866470418736, 16012533919962572, 0]], ![![58035456024, 0, 1062915], ![133, 0, 0]]]]
 g := ![![![![28951161128, -11580429280, 5804824232], ![-1462014324, -165800006605, -50244]], ![![13009698917, -5203863762, 2608496945], ![-656980536, -74505065708, -22578]]], ![![![46816591618, -18726579772, 9386914894], ![-2364207004, -268113294930, -81249]], ![![41319536260, -16527764307, 8284733191], ![-2086609627, -236632284244, -71709]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![800, 0, 0], ![-35, 14, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl

lemma PowJ0_6J1_0 : J0 ^ 6*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![13, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
def MulR61_J0_6J1_1 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) J1
  ![![8, 0, 0], ![13, -2, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![80, 0, 0], ![45, 14, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![80, 0, 0], ![120, 16, 8]], ![![130, -20, 10], ![195, 66, -1]]]
 hmul := by decide
 f := ![![![![1924226, -819247, -91455], ![2713376, -415391, 0]], ![![-109824, 0, 0], ![-144, 0, 0]]], ![![![1082389, -460831, -51444], ![1526290, -233660, 0]], ![![-61776, 0, 0], ![-81, 0, 0]]]]
 g := ![![![![31, 2, 10], ![40, -30, 0]], ![![50, 6, 13], ![32, -38, 0]]], ![![![56, 2, 20], ![90, -60, 0]], ![![28, -1, 13], ![79, -40, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_1 : J0 ^ 6*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![80, 0, 0], ![45, 14, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR61_J0_6J1_1]
 rfl
def MulR62_J0_6J1_2 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![8, 0, 0], ![13, -2, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![800, 0, 0], ![125, 30, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![800, 0, 0], ![360, 16, 8]], ![![1300, -200, 100], ![585, 6, 29]]]
 hmul := by decide
 f := ![![![![1231896670886, 243156714950, 36796133521], ![559584597560, -1059788642660, 0]], ![![-3469440, 0, 0], ![-3040, 0, 0]]], ![![![192483852253, 37993236207, 5749395786], ![87435092268, -165591973224, 0]], ![![-542100, 0, 0], ![-475, 0, 0]]]]
 g := ![![![![97081, 73578, 42828], ![18600, -571350, 0]], ![![43624, 33095, 19272], ![8768, -257106, 0]]], ![![![157831, 119578, 69593], ![29700, -928400, 0]], ![![70944, 53792, 31317], ![13889, -417791, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_2 : J0 ^ 6*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![800, 0, 0], ![125, 30, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR62_J0_6J1_2]
 rfl

lemma PowJ0_7J1_0 : J0 ^ 7*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![13, 6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
def MulR71_J0_7J1_1 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![13, 6, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![160, 0, 0], ![-35, 14, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![160, 0, 0], ![240, 32, 16]], ![![130, 60, 10], ![1315, 18, 31]]]
 hmul := by decide
 f := ![![![![93732489179, -38134266237, -4808368564], ![132491043666, -20760012197, 0]], ![![-2194660704, 0, -870852], ![-288, 0, 0]]], ![![![-20506901409, 8343058467, 1051980384], ![-28986542358, 4541899259, 0]], ![![480150384, 0, 190526], ![63, 0, 0]]]]
 g := ![![![![51522311, -20602414, 10949491], ![-13004740, -62107785, -1860]], ![![75565677, -30216722, 16059169], ![-19073444, -91090941, -2728]]], ![![![38640913, -15451482, 8211943], ![-9753330, -46579845, -1395]], ![![422482761, -168939719, 89785800], ![-106639097, -509283678, -15252]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_1 : J0 ^ 7*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![160, 0, 0], ![-35, 14, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR71_J0_7J1_1]
 rfl
def MulR72_J0_7J1_2 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![16, 0, 0], ![13, 6, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![1600, 0, 0], ![-675, 30, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1600, 0, 0], ![720, 32, 16]], ![![1300, 600, 100], ![1705, 198, 61]]]
 hmul := by decide
 f := ![![![![14807975458075246096, 2922891881417362160, 442305514589731511], ![6726469848908105360, -12739175126059056620, 0]], ![![-51329820808800, 0, -154700964], ![-6080, 0, 0]]], ![![![-6247120371623113684, -1233096142558546624, -186597809977320891], ![-2837732068181345296, 5374344431687913548, 0]], ![![21654787999500, 0, 65264529], ![2565, 0, 0]]]]
 g := ![![![![570670965804, -3472410371475, 300030825398], ![-305671987244, -7995728054755, -49764]], ![![256070310812, -1558132892970, 134629219460], ![-137160509944, -3587826769462, -22330]]], ![![![449952212582, -2737862662800, 236562821404], ![-241010661852, -6304325514890, -39237]], ![![603594325370, -3672741949674, 317340314292], ![-323306928119, -8457020542883, -52635]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_2 : J0 ^ 7*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1600, 0, 0], ![-675, 30, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR72_J0_7J1_2]
 rfl

lemma PowJ0_8J1_0 : J0 ^ 8*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![13, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
def MulR81_J0_8J1_1 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![13, -2, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![160, 0, 0], ![-35, 30, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![160, 0, 0], ![240, 32, 16]], ![![130, -20, 10], ![195, 66, -1]]]
 hmul := by decide
 f := ![![![![162830, -69063, -7819], ![229656, -35231, 0]], ![![-16896, 0, 0], ![-288, 0, 0]]], ![![![-35618, 15101, 1709], ![-50212, 7704, 0]], ![![3696, 0, 0], ![63, 0, 0]]]]
 g := ![![![![14316, -5318, 6543], ![-4080, -17380, 0]], ![![21348, -7932, 9755], ![-6064, -25912, 0]]], ![![![11728, -4364, 5353], ![-3270, -14220, 0]], ![![17200, -6399, 7851], ![-4801, -20856, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_1 : J0 ^ 8*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![160, 0, 0], ![-35, 30, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR81_J0_8J1_1]
 rfl
def MulR82_J0_8J1_2 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![16, 0, 0], ![13, -2, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![1600, 0, 0], ![-355, 62, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1600, 0, 0], ![720, 32, 16]], ![![1300, -200, 100], ![585, 6, 29]]]
 hmul := by decide
 f := ![![![![5027802589206, 992411652902, 150177372417], ![2283861171960, -4325377638660, 0]], ![![-14055680, 0, 0], ![-6080, 0, 0]]], ![![![-1115543704843, -220191336542, -33320604665], ![-506731699892, 959693168168, 0]], ![![3118604, 0, 0], ![1349, 0, 0]]]]
 g := ![![![![42231, -120772, 40006], ![-13200, -516100, 0]], ![![18785, -53873, 17849], ![-6144, -230260, 0]]], ![![![35838, -102210, 33851], ![-10700, -436700, 0]], ![![15594, -44244, 14648], ![-4243, -188972, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_2 : J0 ^ 8*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1600, 0, 0], ![-355, 62, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR82_J0_8J1_2]
 rfl

lemma PowJ0_9J1_0 : J0 ^ 9*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![29, 14, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07]
 rfl     
def MulR91_J0_9J1_1 : IdealMulEqCertificate timesTableO (((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![29, 14, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![320, 0, 0], ![-35, 30, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := rfl
 M := ![![![320, 0, 0], ![480, 64, 32]], ![![290, 140, 10], ![2675, 2, 79]]]
 hmul := by decide
 f := ![![![![273006220376522, -111048209245727, -14220376837807], ![385877651031864, -60486439295073, 0]], ![![-5529855892960, 0, -18202212], ![-576, 0, 0]]], ![![![-29860941199885, 12146258213691, 1555399858684], ![-42206620171190, 6615900563323, 0]], ![![604845931480, 0, 1990926], ![63, 0, 0]]]]
 g := ![![![![2721874, -1062900, 1175961], ![-393504, -6266880, -1764]], ![![3888393, -1518426, 1679948], ![-562208, -8952704, -2520]]], ![![![2041433, -797190, 881978], ![-295038, -4700200, -1323]], ![![22746965, -8882700, 9827678], ![-3289713, -52373212, -14742]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_9J1_1 : J0 ^ 9*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![320, 0, 0], ![-35, 30, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR91_J0_9J1_1]
 rfl
def MulR92_J0_9J1_2 : IdealMulEqCertificate timesTableO (((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![32, 0, 0], ![29, 14, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![3200, 0, 0], ![-355, 62, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3200, 0, 0], ![1440, 64, 32]], ![![2900, 1400, 100], ![3545, 422, 109]]]
 hmul := by decide
 f := ![![![![2689752711567356444476, 530919400126111909592, 80340987286141438967], ![1221810518080694052640, -2313974012565924219580, 0]], ![![-4222836284544480, 0, -2710073124], ![-12160, 0, 0]]], ![![![-298394564317431394677, -58898895205867319650, -8912831947332022569], ![-135544660166434794108, 256706597729988619072, 0]], ![![468471093231552, 0, 300648861], ![1349, 0, 0]]]]
 g := ![![![![694674729, -1892405005, 624677605], ![-113535404, -16121959155, -713124]], ![![312479446, -851243166, 280992972], ![-51067776, -7251992380, -320778]]], ![![![626825903, -1707573373, 563665186], ![-102444308, -14547323360, -643473]], ![![768748487, -2094193714, 691287493], ![-125641607, -17841056951, -789165]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_9J1_2 : J0 ^ 9*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3200, 0, 0], ![-355, 62, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR92_J0_9J1_2]
 rfl

lemma PowJ0_10J1_0 : J0 ^ 10*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![29, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08]
 rfl     
def MulR101_J0_10J1_1 : IdealMulEqCertificate timesTableO ((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![29, -2, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![320, 0, 0], ![-35, 62, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![320, 0, 0], ![480, 64, 32]], ![![290, -20, 10], ![435, 98, 15]]]
 hmul := by decide
 f := ![![![![61197857, -25541421, -3166190], ![86371894, -13373631, 0]], ![![-3888640, 0, 0], ![-576, 0, 0]]], ![![![-6693508, 2793587, 346301], ![-9446904, 1462738, 0]], ![![425320, 0, 0], ![63, 0, 0]]]]
 g := ![![![![8891, -3346, 8014], ![-1400, -20670, 0]], ![![12990, -4882, 11713], ![-2088, -30210, 0]]], ![![![8192, -3062, 7398], ![-1430, -19080, 0]], ![![11476, -4299, 10357], ![-1937, -26712, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_10J1_1 : J0 ^ 10*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![320, 0, 0], ![-35, 62, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR101_J0_10J1_1]
 rfl
def MulR102_J0_10J1_2 : IdealMulEqCertificate timesTableO ((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![32, 0, 0], ![29, -2, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![3200, 0, 0], ![285, 126, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3200, 0, 0], ![1440, 64, 32]], ![![2900, -200, 100], ![1305, 38, 45]]]
 hmul := by decide
 f := ![![![![97907045439706, 19325404451726, 2924413181909], ![44473922668840, -84228711630660, 0]], ![![-126182400, 0, 0], ![-12160, 0, 0]]], ![![![8719846223525, 1721168831826, 260455548687], ![3960958732812, -7501619620216, 0]], ![![-11238120, 0, 0], ![-1083, 0, 0]]]]
 g := ![![![![2671, 5112, 4902], ![600, -62250, 0]], ![![1194, 2297, 2206], ![360, -28014, 0]]], ![![![2317, 4586, 4441], ![1700, -56400, 0]], ![![1065, 2074, 1999], ![517, -25386, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_10J1_2 : J0 ^ 10*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3200, 0, 0], ![285, 126, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR102_J0_10J1_2]
 rfl

lemma PowJ0_11J1_0 : J0 ^ 11*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64, 0, 0], ![29, 30, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09]
 rfl     
def MulR111_J0_11J1_1 : IdealMulEqCertificate timesTableO (((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![64, 0, 0], ![29, 30, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![640, 0, 0], ![285, 62, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := rfl
 M := ![![![640, 0, 0], ![960, 128, 64]], ![![290, 300, 10], ![4915, -94, 143]]]
 hmul := by decide
 f := ![![![![-1706192987758566, 690582238990369, 88985706116289], ![-2412274463228136, 378998408613335, 0]], ![![41112366159648, 0, -31678372], ![-1152, 0, 0]]], ![![![-759782438442345, 307522221254914, 39626101657097], ![-1074206603246810, 168771256902360, 0]], ![![18307690885512, 0, -14106652], ![-513, 0, 0]]]]
 g := ![![![![4298885340, 10273294924, 4953535840], ![2917312916, -25590138435, -11684]], ![![6354874765, 15186611934, 7322619193], ![4312550292, -37828905435, -17272]]], ![![![1728901590, 4131656317, 1992185359], ![1173268806, -10291698855, -4699]], ![![33082725910, 79059702604, 38120687943], ![22450624067, -196932799755, -89916]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_11J1_1 : J0 ^ 11*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![640, 0, 0], ![285, 62, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR111_J0_11J1_1]
 rfl
def MulR112_J0_11J1_2 : IdealMulEqCertificate timesTableO (((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![64, 0, 0], ![29, 30, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![6400, 0, 0], ![14565, -1746, 1129]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![6400, 0, 0], ![2880, 128, 64]], ![![2900, 3000, 100], ![5785, 806, 173]]]
 hmul := by decide
 f := ![![![![14529070764282767319406, 2867839425941140107684, 433972895151723173713], ![6599778361397585327640, -12499255593487020259100, 0]], ![![-29121643188522720, 0, -4347162404], ![-24320, 0, 0]]], ![![![33064998487109074869869, 6526577495453242779772, 987627726125018346469], ![15019657146369398730604, -28445581551205285722616, 0]], ![![-66274512912262512, 0, -9893194179], ![-55347, 0, 0]]]]
 g := ![![![![3063512139481, 740017392751, -1540724521963], ![6498204071284, -722843674395, 608804]], ![![1377293268984, 332696895538, -692678671968], ![2921461496056, -324975937662, 273706]]], ![![![1357985422781, 328032920465, -682968223839], ![2880506430424, -320420200545, 269869]], ![![2761022499289, 666948448187, -1388594159424], ![5856574676981, -651470454534, 548691]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_11J1_2 : J0 ^ 11*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6400, 0, 0], ![14565, -1746, 1129]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR112_J0_11J1_2]
 rfl

lemma PowJ0_12J1_0 : J0 ^ 12*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64, 0, 0], ![29, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010]
 rfl     
def MulR121_J0_12J1_1 : IdealMulEqCertificate timesTableO ((((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![64, 0, 0], ![29, -2, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![640, 0, 0], ![285, 126, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010
 hI2 := rfl
 M := ![![![640, 0, 0], ![960, 128, 64]], ![![290, -20, 10], ![435, 98, 15]]]
 hmul := by decide
 f := ![![![![-121913752, 50882405, 6307419], ![-172063396, 26641729, 0]], ![![15504384, 0, 0], ![-1152, 0, 0]]], ![![![-54289717, 22658564, 2808771], ![-76621954, 11863892, 0]], ![![6904296, 0, 0], ![-513, 0, 0]]]]
 g := ![![![![-259, -66, 60], ![660, -155, 0]], ![![-188, -10, 91], ![540, -233, 0]]], ![![![-149, -44, 27], ![370, -70, 0]], ![![-193, -52, 41], ![487, -106, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_12J1_1 : J0 ^ 12*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![640, 0, 0], ![285, 126, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR121_J0_12J1_1]
 rfl
def MulR122_J0_12J1_2 : IdealMulEqCertificate timesTableO ((((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![64, 0, 0], ![29, -2, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![6400, 0, 0], ![285, 126, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![6400, 0, 0], ![2880, 128, 64]], ![![2900, -200, 100], ![1305, 38, 45]]]
 hmul := by decide
 f := ![![![![393590620103256, 77689029568506, 11756267994379], ![178787122317840, -338603282654660, 0]], ![![-506316800, 0, 0], ![-24320, 0, 0]]], ![![![17527082290535, 3459589595814, 523521308798], ![7961614035756, -15078427421308, 0]], ![![-22546920, 0, 0], ![-1083, 0, 0]]]]
 g := ![![![![6871, 13032, 12462], ![1200, -316500, 0]], ![![3084, 5861, 5608], ![720, -142428, 0]]], ![![![3026, 5866, 5646], ![2500, -143400, 0]], ![![1380, 2648, 2541], ![717, -64536, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_12J1_2 : J0 ^ 12*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6400, 0, 0], ![285, 126, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR122_J0_12J1_2]
 rfl

lemma PowJ0_13J1_0 : J0 ^ 13*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![128, 0, 0], ![29, 62, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ011]
 rfl     
def MulR131_J0_13J1_1 : IdealMulEqCertificate timesTableO (((((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![128, 0, 0], ![29, 62, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![1280, 0, 0], ![-4865, -406, -309]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ011
 hI2 := rfl
 M := ![![![1280, 0, 0], ![1920, 256, 128]], ![![290, 620, 10], ![9395, -286, 271]]]
 hmul := by decide
 f := ![![![![-81649717177866940, 32939984665609485, 4261975537834855], ![-115460381279894996, 18167708439888611, 0]], ![![2173342602106144, 0, -398068260], ![-2304, 0, 0]]], ![![![310332548214872245, -125197609162183564, -16198828052331227], ![438839417684638554, -69051448679160824, 0]], ![![-8260395395936152, 0, 1512969570], ![8757, 0, 0]]]]
 g := ![![![![3014664679321, -4543973529354, -1581969578106], ![-9634892025240, 1172734942050, 121380]], ![![4509330346799, -6796867954986, -2366307431696], ![-14411855270488, 1754174951802, 181560]]], ![![![652332881393, -983254737021, -342316932709], ![-2084861005850, 253764063540, 26265]], ![![22141318725532, -33373385442839, -11618835398614], ![-70763828880579, 8613196135020, 891480]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_13J1_1 : J0 ^ 13*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1280, 0, 0], ![-4865, -406, -309]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR131_J0_13J1_1]
 rfl
def MulR132_J0_13J1_2 : IdealMulEqCertificate timesTableO (((((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![128, 0, 0], ![29, 62, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![12800, 0, 0], ![-61205, -3278, -4441]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ011
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![12800, 0, 0], ![5760, 256, 128]], ![![2900, 6200, 100], ![10265, 1574, 301]]]
 hmul := by decide
 f := ![![![![16006253182602833886901, 3159434728759729697798, 478095283658678261540], ![7270783579583056625740, -13770063841217103761740, 0]], ![![-72422255576920800, 0, -111247703844], ![-48640, 0, 0]]], ![![![-76536149529064360423764, -15107281264955714501989, -2286079802799342829081], ![-34766273711406069909008, 65843495860832993005592, 0]], ![![346297195154448480, 0, 531946533585], ![232579, 0, 0]]]]
 g := ![![![![263914418244303898, -527589517537076364, -300448434999787056], ![-1022590002368786516, 106098571181597555, 4493604]], ![![118731429620385101, -237355192969833314, -135167576110620919], ![-460049032957156576, 47732272912078908, 2021610]]], ![![![59065128917620339, -118076697272554730, -67241591665984729], ![-228859835402535548, 23745295260874640, 1005687]], ![![211462179084341976, -422732603177283699, -240735164036072316], ![-819353151105853377, 85011782262780239, 3600513]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_13J1_2 : J0 ^ 13*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12800, 0, 0], ![-61205, -3278, -4441]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR132_J0_13J1_2]
 rfl

lemma PowJ0_14J1_0 : J0 ^ 14*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![128, 0, 0], ![29, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ012]
 rfl     
def MulR141_J0_14J1_1 : IdealMulEqCertificate timesTableO ((((((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![128, 0, 0], ![29, -2, 1]] ![![10, 0, 0], ![15, 2, 1]]
  ![![1280, 0, 0], ![285, 126, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ012
 hI2 := rfl
 M := ![![![1280, 0, 0], ![1920, 256, 128]], ![![290, -20, 10], ![435, 98, 15]]]
 hmul := by decide
 f := ![![![![-248197627, 103588491, 12840942], ![-350294626, 54238529, 0]], ![![63121408, 0, 0], ![-2304, 0, 0]]], ![![![-55262756, 23064621, 2859115], ![-77995272, 12076546, 0]], ![![14054376, 0, 0], ![-513, 0, 0]]]]
 g := ![![![![26, 60, 61], ![40, -310, 0]], ![![-188, -10, 91], ![1080, -466, 0]]], ![![![-217, -85, 13], ![1010, -70, 0]], ![![-239, -89, 20], ![1127, -106, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_14J1_1 : J0 ^ 14*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1280, 0, 0], ![285, 126, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR141_J0_14J1_1]
 rfl
def MulR142_J0_14J1_2 : IdealMulEqCertificate timesTableO ((((((((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![128, 0, 0], ![29, -2, 1]] ![![100, 0, 0], ![45, 2, 1]]
  ![![12800, 0, 0], ![-6115, 126, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ012
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![12800, 0, 0], ![5760, 256, 128]], ![![2900, -200, 100], ![1305, 38, 45]]]
 hmul := by decide
 f := ![![![![37065265520416, 7316143694282, 1107112688627], ![16836763485040, -31886998782660, 0]], ![![-47616000, 0, 0], ![-48640, 0, 0]]], ![![![-17707351468608, -3495173337361, -528905788684], ![-8043500685392, 15233515443476, 0]], ![![22747800, 0, 0], ![23237, 0, 0]]]]
 g := ![![![![2388141, -161797486, 6646194], ![-2729700, -337573625, 0]], ![![1076564, -72810441, 2990850], ![-1224460, -151911331, 0]]], ![![![545208, -36653735, 1505630], ![-609600, -76474025, 0]], ![![248406, -16495777, 677596], ![-267983, -34416511, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_14J1_2 : J0 ^ 14*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12800, 0, 0], ![-6115, 126, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR142_J0_14J1_2]
 rfl
