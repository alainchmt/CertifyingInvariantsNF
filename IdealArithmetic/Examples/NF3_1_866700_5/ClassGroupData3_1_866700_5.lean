import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_866700_5.RI3_1_866700_5

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-161, -20, -13]

def alpha1 := B.equivFun.symm ![-89, -11, -7]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-27, 61, -91]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![-1, 1, 0]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![49, 0, 0], ![-8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![-7, 7, 0]], ![![-7, 7, 0], ![-5, 4, 13]]]
 hmul := by decide
 f := ![![![![-5329378, 4411216, 12058787], ![1391516, -6296500, 0]], ![![0, 0, 0], ![-1377243, -196, 0]]], ![![![924479, -765207, -2091817], ![-241377, 1092243, 0]], ![![0, 0, 0], ![238908, 34, 0]]]]
 g := ![![![![-451, -158, 1014], ![98, -3822, 0]], ![![79, 26, -169], ![7, 637, 0]]], ![![![79, 26, -169], ![7, 637, 0]], ![![55, 18, -117], ![6, 442, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![-8, 1, 0]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![-161, -20, -13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![-49, 49, 0]], ![![-56, 7, 0], ![2, -3, 13]]]
 hmul := by decide
 f := ![![![![19473442967, -15728616772, -42592629027], ![-5028865670, 22933023374, 0]], ![![3268211952, 11107942, 0], ![-5760388, 604, 0]]]]
 g := ![![![![-315, 14, 13]], ![![371, -35, 13]]], ![![![98, -7, 0]], ![![-8, 9, -13]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![13, 0, 0], ![1, 1, 0]] ![![13, 0, 0], ![1, 1, 0]]
  ![![169, 0, 0], ![-64, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![169, 0, 0], ![13, 13, 0]], ![![13, 13, 0], ![-5, 8, 13]]]
 hmul := by decide
 f := ![![![![57013528962, -334202467, -1573617906], ![4359948203, 0, -4096402168]], ![![0, 0, 0], ![-24986312, 0, 4290]]], ![![![-21596033422, 126591841, 596067381], ![-1651495498, 0, 1551667468]], ![![0, 0, 0], ![9464512, 0, -1625]]]]
 g := ![![![![111201, -266117, 0], ![-43507, -776160, -144144]], ![![8469, -20161, 0], ![-3178, -58800, -10920]]], ![![![8469, -20161, 0], ![-3178, -58800, -10920]], ![![-3335, 8064, 0], ![1410, 23521, 4368]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![169, 0, 0], ![-64, 1, 0]] ![![13, 0, 0], ![1, 1, 0]]
  ![![-89, -11, -7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![2197, 0, 0], ![169, 169, 0]], ![![-832, 13, 0], ![-70, -57, 13]]]
 hmul := by decide
 f := ![![![![1382551936881044509, -8123644571567617, -38218326290372706], ![105725253254575146, 0, -99376715573543264]], ![![-1532360335344057, 0, 8419558081032], ![-141591895, 0, -2255]]]]
 g := ![![![![-177, 29, -26]], ![![-391, 2, 39]]], ![![![38, -11, 13]], ![![190, -3, -16]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1387565, 173213, 112528])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![-64, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![7, 0, 0], ![-1, 1, 0]] ![![13, 0, 0], ![1, 1, 0]]
  ![![91, 0, 0], ![27, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![91, 0, 0], ![7, 7, 0]], ![![-13, 13, 0], ![-7, 6, 13]]]
 hmul := by decide
 f := ![![![![-5459443, 29873, 150579], ![-417651, 0, 392418]], ![![14833, 189, 0], ![0, 0, 0]]], ![![![-1617613, 8851, 44616], ![-123745, 0, 116272]], ![![4395, 56, 0], ![0, 0, 0]]]]
 g := ![![![![152037346, -893389839, -351771966], ![35292579, 2462520690, -72384]], ![![11877889, -69796057, -27482175], ![2757314, 192384360, -5655]]], ![![![-21380278, 125632992, 49467951], ![-4962959, -346292100, 10179]], ![![-11877943, 69796088, 27482188], ![-2757152, -192384450, 5655]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![91, 0, 0], ![27, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![7, 0, 0], ![-1, 1, 0]] ![![169, 0, 0], ![-64, 1, 0]]
  ![![1183, 0, 0], ![-64, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1183, 0, 0], ![-448, 7, 0]], ![![-169, 169, 0], ![58, -59, 13]]]
 hmul := by decide
 f := ![![![![152714758169063, -365660918355493, 0], ![-59996481900299, -1066494123731070, -198063193415724]], ![![1345362018, 221130, 0], ![0, 0, 0]]], ![![![-8266610815828, 19793610904738, 0], ![3247672799559, 57730450966050, 10721369411454]], ![![-72825864, -11970, 0], ![0, 0, 0]]]]
 g := ![![![![127329, -266369, 0], ![-6433, -5433120, -1009008]], ![![-48208, 100897, 0], ![2856, 2058000, 382200]]], ![![![-18439, 38629, 0], ![1422, 787920, 146328]], ![![6352, -13261, 0], ![-78, -270479, -50232]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1183, 0, 0], ![-64, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![-8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![49, 0, 0], ![-8, 1, 0]] ![![13, 0, 0], ![1, 1, 0]]
  ![![637, 0, 0], ![-155, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![637, 0, 0], ![49, 49, 0]], ![![-104, 13, 0], ![-14, -1, 13]]]
 hmul := by decide
 f := ![![![![-277354597403, 1515744060, 7687742400], ![-21218373332, 0, 19994457600]], ![![5723832296, 9172800, 0], ![0, 0, 0]]], ![![![67489618701, -368831055, -1870683984], ![5163137516, 0, -4865318016]], ![![-1392799192, -2232048, 0], ![0, 0, 0]]]]
 g := ![![![![77906218906, 2029964663491, -177109700105], ![-15770014267, 8678333695500, -3359785]], ![![6316720132, 164591720137, -14360245140], ![-1278649575, 703648638105, -272415]]], ![![![-12633440862, -329183461422, 28720492125], ![2557300192, -1407297366615, 544830]], ![![-1722741912, -44888653196, 3916430689], ![348722746, -191904183645, 74295]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![637, 0, 0], ![-155, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![49, 0, 0], ![-8, 1, 0]] ![![169, 0, 0], ![-64, 1, 0]]
  ![![8281, 0, 0], ![1119, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![8281, 0, 0], ![-3136, 49, 0]], ![![-1352, 169, 0], ![506, -66, 13]]]
 hmul := by decide
 f := ![![![![2981545702011838089, -7139029708571124554, 0], ![-1171348844007862321, -20821851002014610400, -3866915186010578520]], ![![3327511392387, 121539600, 0], ![0, 0, 0]]], ![![![402890919220654655, -964684270876342462, 0], ![-158282266869812038, -2813619353349716868, -522529308468713520]], ![![449640641997, 16423428, 0], ![0, 0, 0]]]]
 g := ![![![![583792, -82151263, 0], ![70903, 604706256, -7063056]], ![![-221869, 31117902, 0], ![-21413, -229055400, 2675400]]], ![![![-96044, 13437853, 0], ![-7524, -98914536, 1155336]], ![![34967, -5029670, 0], ![10079, 37022833, -432432]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8281, 0, 0], ![1119, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
