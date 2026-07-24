import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_662796_1.RI3_1_662796_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-80, 12, 3]

def alpha1 := B.equivFun.symm ![-44, 11, 7]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-30, 8, 3]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![17, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![17, 0, 1]] ![![5, 0, 0], ![17, 0, 1]]
  ![![25, 0, 0], ![27, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![85, 0, 5]], ![![85, 0, 5], ![260, 13, 12]]]
 hmul := by decide
 f := ![![![![-133796, 116000, 125299], ![-429835, 96000, 0]], ![![0, 0, 0], ![-1500, -50, 0]]], ![![![-144499, 125280, 135323], ![-464222, 103680, 0]], ![![0, 0, 0], ![-1620, -54, 0]]]]
 g := ![![![![-26, 0, -1], ![25, 0, 0]], ![![-2, 0, 0], ![5, 0, 0]]], ![![![-2, 0, 0], ![5, 0, 0]], ![![-394, -39, 36], ![-394, 247, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![27, 0, 1]] ![![5, 0, 0], ![17, 0, 1]]
  ![![125, 0, 0], ![2, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![425, 0, 25]], ![![135, 0, 5], ![430, 13, 22]]]
 hmul := by decide
 f := ![![![![-296591874, 283100000, 299616665], ![-948489015, 235600000, 0]], ![![-396932250, -2400000, 0], ![37500, -250, 0]]], ![![![-4745481, 4529600, 4793866], ![-15175821, 3769600, 0]], ![![-6350916, -38400, 0], ![600, -4, 0]]]]
 g := ![![![![-1, 0, -1], ![125, 0, 0]], ![![3, 0, 0], ![25, 0, 0]]], ![![![1, 0, 0], ![5, 0, 0]], ![![54, -13, -2], ![116, -78, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![125, 0, 0], ![2, 0, 1]] ![![5, 0, 0], ![17, 0, 1]]
  ![![625, 0, 0], ![-248, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![625, 0, 0], ![2125, 0, 125]], ![![10, 0, 5], ![5, 13, -3]]]
 hmul := by decide
 f := ![![![![-6515153955, 5617500000, 6717585697], ![-20808006300, 4680000000, 0]], ![![-85479768125, 9000000, 0], ![562500, 1875, 0]]], ![![![2585213082, -2229024000, -2665538005], ![8256616902, -1857024000, 0]], ![![33918371992, -3571200, 0], ![-223200, -744, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![53, 0, 0], ![125, 0, 0]]], ![![![2, 0, 0], ![5, 0, 0]], ![![533, -1443, -11], ![216, -3328, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![625, 0, 0], ![-248, 0, 1]] ![![5, 0, 0], ![17, 0, 1]]
  ![![3125, 0, 0], ![-248, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![3125, 0, 0], ![10625, 0, 625]], ![![-1240, 0, 5], ![-4245, 13, -253]]]
 hmul := by decide
 f := ![![![![824540226801458, -603738960000000, -738055945095014], ![2655825582106005, -503088960000000, 0]], ![![3534381636940625, -74280000000, 0], ![45000000, 9375, 0]]], ![![![-65435512398969, 47912723865600, 58572119802740], ![-210766318195931, 39925139865600, 0]], ![![-280488526707608, 5894860800, 0], ![-3571200, -744, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![53, 0, 0], ![625, 0, 0]]], ![![![0, 0, 0], ![5, 0, 0]], ![![959, -3107, -23], ![-34, -35828, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![3125, 0, 0], ![-248, 0, 1]] ![![5, 0, 0], ![17, 0, 1]]
  ![![15625, 0, 0], ![6002, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![15625, 0, 0], ![53125, 0, 3125]], ![![-1240, 0, 5], ![-4245, 13, -253]]]
 hmul := by decide
 f := ![![![![-1209748468113213, 1248683400000000, 1179228367350998], ![-3877299118114680, 1040558400000000, 0]], ![![38921619428843750, 153600000000, 0], ![225000000, 46875, 0]]], ![![![-464698259559395, 479654257075200, 452974634293804], ![-1489379155643155, 399707617075200, 0]], ![![14950883827962892, 59002060800, 0], ![86428800, 18006, 0]]]]
 g := ![![![![-6001, 0, -1], ![15625, 0, 0]], ![![-1197, 0, 0], ![3125, 0, 0]]], ![![![-2, 0, 0], ![5, 0, 0]], ![![-5033, -17381, 5], ![12466, 45422, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![15625, 0, 0], ![6002, 0, 1]] ![![5, 0, 0], ![17, 0, 1]]
  ![![78125, 0, 0], ![6002, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![78125, 0, 0], ![265625, 0, 15625]], ![![30010, 0, 5], ![102005, 13, 5997]]]
 hmul := by decide
 f := ![![![![115567546565116893925, -122797725299875000000, -114976958544812569538], ![369934266612434925500, -102331219440500000000, 0]], ![![900273944754232968750, 684613000000000, 0], ![16828125000, -156250, 0]]], ![![![8878546105393044434, -9434008924798076800, -8833173826380352543], ![28420421993060280616, -7861657332248076800, 0]], ![![69164085970110800364, 52595804492800, 0], ![1292830800, -12004, 0]]]]
 g := ![![![![-6001, 0, -1], ![78125, 0, 0]], ![![-1197, 0, 0], ![15625, 0, 0]]], ![![![0, 0, 0], ![5, 0, 0]], ![![-4323, -34567, 11], ![49966, 451672, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![78125, 0, 0], ![6002, 0, 1]] ![![5, 0, 0], ![17, 0, 1]]
  ![![390625, 0, 0], ![162252, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![390625, 0, 0], ![1328125, 0, 78125]], ![![30010, 0, 5], ![102005, 13, 5997]]]
 hmul := by decide
 f := ![![![![-167590718657530913860, 140619719541875000000, 154643967171795146732], ![-538879650001246077725, 117183049620000000000, 0]], ![![404894929121506640625, -783966250000000, 0], ![84140625000, -781250, 0]]], ![![![-69611338966071566935, 58408526681877254400, 64233709981588751738], ![-223831810488325577225, 48673751467377254400, 0]], ![![168179230821946100364, -325632235507200, 0], ![34949080800, -324504, 0]]]]
 g := ![![![![-162251, 0, -1], ![390625, 0, 0]], ![![-32447, 0, 0], ![78125, 0, 0]]], ![![![-2, 0, 0], ![5, 0, 0]], ![![-118639, -1031173, 12], ![284341, 2482922, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![390625, 0, 0], ![162252, 0, 1]] ![![5, 0, 0], ![17, 0, 1]]
  ![![-80, 12, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![1953125, 0, 0], ![6640625, 0, 390625]], ![![811260, 0, 5], ![2758255, 13, 162247]]]
 hmul := by decide
 f := ![![![![-2038388537028732427240, 2158021205118442960192, 2024501388104448139439], ![-6525620748276800624684, 1798350850806017960192, 0]], ![![-14413331606359331066400, -443410677876576, 0], ![-467232036, 160, 0]]]]
 g := ![![![![-48268, -1329, -1743]], ![![-176329, -2937, -7379]]], ![![![-20049, -552, -724]], ![![-73241, -1220, -3065]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow9 : J0 ^ 9 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![35, 0, 0], ![27, 0, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![35, 0, 0], ![27, 0, 1]] ![![35, 0, 0], ![27, 0, 1]]
  ![![1225, 0, 0], ![27, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![1225, 0, 0], ![945, 0, 35]], ![![945, 0, 35], ![700, 13, 32]]]
 hmul := by decide
 f := ![![![![-26182221, -2082500, 1794614], ![-20146420, 18742500, 0]], ![![0, 0, 0], ![-5622750, -20825, 0]]], ![![![-577098, -45900, 39554], ![-444017, 413100, 0]], ![![0, 0, 0], ![-123930, -459, 0]]]]
 g := ![![![![-26, 0, -1], ![1225, 0, 0]], ![![0, 0, 0], ![35, 0, 0]]], ![![![0, 0, 0], ![35, 0, 0]], ![![-833, -39, 19], ![651, 11947, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![1225, 0, 0], ![27, 0, 1]] ![![35, 0, 0], ![27, 0, 1]]
  ![![-44, 11, 7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![42875, 0, 0], ![33075, 0, 1225]], ![![945, 0, 35], ![700, 13, 32]]]
 hmul := by decide
 f := ![![![![-10419546, -74910, -290297], ![-8046190, 674190, 0]], ![![682889064, -674190, 0], ![202257, 748, 0]]]]
 g := ![![![![-55812, -1286, -2337]], ![![-44205, -1015, -1855]]], ![![![-1263, -29, -53]], ![![-1000, -23, -42]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![20026, 461, 841])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![35, 0, 0], ![27, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1225, 0, 0], ![27, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![17, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![17, 0, 1]] ![![35, 0, 0], ![27, 0, 1]]
  ![![175, 0, 0], ![27, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![175, 0, 0], ![135, 0, 5]], ![![595, 0, 35], ![430, 13, 22]]]
 hmul := by decide
 f := ![![![![1818834, 140000, -118421], ![1399755, -1260000, 0]], ![![0, 0, 0], ![52500, -350, 0]]], ![![![280611, 21600, -18271], ![215974, -194400, 0]], ![![0, 0, 0], ![8100, -54, 0]]]]
 g := ![![![![-26, 0, -1], ![175, 0, 0]], ![![0, 0, 0], ![5, 0, 0]]], ![![![-2, 0, 0], ![35, 0, 0]], ![![-290, -13, 6], ![116, 572, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![175, 0, 0], ![27, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![5, 0, 0], ![17, 0, 1]] ![![1225, 0, 0], ![27, 0, 1]]
  ![![6125, 0, 0], ![1252, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![6125, 0, 0], ![135, 0, 5]], ![![20825, 0, 1225], ![430, 13, 22]]]
 hmul := by decide
 f := ![![![![1954110162, 93100000, -46593557], ![43033025, -28513100000, 0]], ![![0, 0, 0], ![1837500, -12250, 0]]], ![![![399436053, 19030400, -9524104], ![8797029, -5828310400, 0]], ![![0, 0, 0], ![375600, -2504, 0]]]]
 g := ![![![![-1251, 0, -1], ![6125, 0, 0]], ![![-1, 0, 0], ![5, 0, 0]]], ![![![-247, 0, 0], ![1225, 0, 0]], ![![-982, -8788, 14], ![1866, 43797, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6125, 0, 0], ![1252, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![27, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![27, 0, 1]] ![![35, 0, 0], ![27, 0, 1]]
  ![![875, 0, 0], ![377, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![875, 0, 0], ![675, 0, 25]], ![![945, 0, 35], ![700, 13, 32]]]
 hmul := by decide
 f := ![![![![-1047679905, 18060000, -61881078], ![-809978225, -162540000, 0]], ![![1899778125, 3220000, 0], ![52500, -1750, 0]]], ![![![-451400385, 7781280, -26661905], ![-348984885, -70031520, 0]], ![![818532975, 1387360, 0], ![22620, -754, 0]]]]
 g := ![![![![-376, 0, -1], ![875, 0, 0]], ![![-10, 0, 0], ![25, 0, 0]]], ![![![-14, 0, 0], ![35, 0, 0]], ![![-982, -3913, 22], ![126, 9672, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![875, 0, 0], ![377, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![25, 0, 0], ![27, 0, 1]] ![![1225, 0, 0], ![27, 0, 1]]
  ![![30625, 0, 0], ![13502, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![30625, 0, 0], ![675, 0, 25]], ![![33075, 0, 1225], ![700, 13, 32]]]
 hmul := by decide
 f := ![![![![-1272746942, -60637500, 30343291], ![-28026775, 18570387500, 0]], ![![0, 0, 0], ![-1225000, -61250, 0]]], ![![![-561130768, -26733960, 13377799], ![-12355662, 8187342760, 0]], ![![0, 0, 0], ![-540080, -27004, 0]]]]
 g := ![![![![-13501, 0, -1], ![30625, 0, 0]], ![![-11, 0, 0], ![25, 0, 0]]], ![![![-539, 0, 0], ![1225, 0, 0]], ![![-9922, -159458, 23], ![20251, 362297, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![30625, 0, 0], ![13502, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![125, 0, 0], ![2, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![125, 0, 0], ![2, 0, 1]] ![![35, 0, 0], ![27, 0, 1]]
  ![![4375, 0, 0], ![377, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![4375, 0, 0], ![3375, 0, 125]], ![![70, 0, 35], ![25, 13, 7]]]
 hmul := by decide
 f := ![![![![24867883590, 5297600000, -41392751018], ![18001145925, -47678400000, 0]], ![![4767441721875, -900900000, 0], ![2887500, -8750, 0]]], ![![![2142901047, 456501760, -3566872488], ![1551184470, -4108515840, 0]], ![![410817263805, -77631840, 0], ![248820, -754, 0]]]]
 g := ![![![![-376, 0, -1], ![4375, 0, 0]], ![![-10, 0, 0], ![125, 0, 0]]], ![![![-3, 0, 0], ![35, 0, 0]], ![![-639, -1703, 9], ![2726, 21047, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4375, 0, 0], ![377, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![125, 0, 0], ![2, 0, 1]] ![![1225, 0, 0], ![27, 0, 1]]
  ![![153125, 0, 0], ![74752, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![153125, 0, 0], ![3375, 0, 125]], ![![2450, 0, 1225], ![25, 13, 7]]]
 hmul := by decide
 f := ![![![![-72957790267840, -3462872875000, 1596385293142], ![-1606746082375, 1060506552875000, 0]], ![![17045768578125, 33687500, 0], ![-67375000, -306250, 0]]], ![![![-35616266044760, -1690492559360, 779317508133], ![-784375399480, 517714193244160, 0]], ![![8321340687360, 16445440, 0], ![-32890880, -149504, 0]]]]
 g := ![![![![-74751, 0, -1], ![153125, 0, 0]], ![![-61, 0, 0], ![125, 0, 0]]], ![![![-598, 0, 0], ![1225, 0, 0]], ![![-40847, -953992, 25], ![81476, 1954797, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![153125, 0, 0], ![74752, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![625, 0, 0], ![-248, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![625, 0, 0], ![-248, 0, 1]] ![![35, 0, 0], ![27, 0, 1]]
  ![![21875, 0, 0], ![9127, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![21875, 0, 0], ![16875, 0, 625]], ![![-8680, 0, 35], ![-6725, 13, -243]]]
 hmul := by decide
 f := ![![![![-15743056960748, -150349500000, 512034795488], ![-12130014375535, 1353145500000, 0]], ![![-55069427503125, 9906750000, 0], ![-218531250, 65625, 0]]], ![![![-6568543125985, -62730966240, 213638472156], ![-5061057883670, 564578696160, 0]], ![![-22976853248961, 4133435760, 0], ![-91178730, 27381, 0]]]]
 g := ![![![![-9126, 0, -1], ![21875, 0, 0]], ![![-260, 0, 0], ![625, 0, 0]]], ![![![-15, 0, 0], ![35, 0, 0]], ![![-7464, -103441, 22], ![15601, 248547, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![21875, 0, 0], ![9127, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![625, 0, 0], ![-248, 0, 1]] ![![1225, 0, 0], ![27, 0, 1]]
  ![![765625, 0, 0], ![381002, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![765625, 0, 0], ![16875, 0, 625]], ![![-303800, 0, 1225], ![-6725, 13, -243]]]
 hmul := by decide
 f := ![![![![3269910268247739071, 155673697400156250, -77905126814353940], ![72007895604796200, -47675085402397031250, 0]], ![![5918980936312500, -117278437500, 0], ![39092812500, 17609375, 0]]], ![![![1627222663866677656, 77468721706911780, -38768338450968137], ![35833668233428394, -23724803772713892180, 0]], ![![2945493648583752, -58361886360, 0], ![19453962120, 8763046, 0]]]]
 g := ![![![![-381001, 0, -1], ![765625, 0, 0]], ![![-311, 0, 0], ![625, 0, 0]]], ![![![-610, 0, 0], ![1225, 0, 0]], ![![-193473, -2953808, 15], ![387476, 5936047, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![765625, 0, 0], ![381002, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3125, 0, 0], ![-248, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![3125, 0, 0], ![-248, 0, 1]] ![![35, 0, 0], ![27, 0, 1]]
  ![![109375, 0, 0], ![52877, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![109375, 0, 0], ![84375, 0, 3125]], ![![-8680, 0, 35], ![-6725, 13, -243]]]
 hmul := by decide
 f := ![![![![-126663937580189, -1255826250000, 4139407031805], ![-97593911646630, 11302436250000, 0]], ![![-2202792762515625, 413752500000, 0], ![-1092656250, 328125, 0]]], ![![![-61235282536486, -607125253680, 2001183319961], ![-47181469861835, 5464127283120, 0]], ![![-1064933237975211, 200027345760, 0], ![-528241230, 158631, 0]]]]
 g := ![![![![-52876, 0, -1], ![109375, 0, 0]], ![![-1510, 0, 0], ![3125, 0, 0]]], ![![![-17, 0, 0], ![35, 0, 0]], ![![-28884, -120107, 4], ![59351, 248547, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![109375, 0, 0], ![52877, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![3125, 0, 0], ![-248, 0, 1]] ![![1225, 0, 0], ![27, 0, 1]]
  ![![3828125, 0, 0], ![-384623, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3828125, 0, 0], ![84375, 0, 3125]], ![![-303800, 0, 1225], ![-6725, 13, -243]]]
 hmul := by decide
 f := ![![![![152599595735092454493, 7267016765974218750, -3636519190363297929], ![3360451074005823350, -2225524029931567968750, 0]], ![![835441281257734375, -5472993750000, 0], ![195464062500, 88046875, 0]]], ![![![-15332131085170537842, -730138589930919690, 365371799655210511], ![-337634422448937649, 223604957770284268890, 0]], ![![-83939247522270973, 549887810640, 0], ![-19638850380, -8846329, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![314, 0, 0], ![3125, 0, 0]]], ![![![123, 0, 0], ![1225, 0, 0]], ![![193305, -2403791, -13], ![1918726, -23923328, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3828125, 0, 0], ![-384623, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl

lemma PowJ0_6J1_0 : J0 ^ 6*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![15625, 0, 0], ![6002, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
def MulR61_J0_6J1_1 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) J1
  ![![15625, 0, 0], ![6002, 0, 1]] ![![35, 0, 0], ![27, 0, 1]]
  ![![546875, 0, 0], ![162252, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![546875, 0, 0], ![421875, 0, 15625]], ![![210070, 0, 35], ![162025, 13, 6007]]]
 hmul := by decide
 f := ![![![![6589924524298515322935, -39847146325000000, -143358829148562268658], ![5079560095054610041450, 358624316925000000, 0]], ![![-27358856928561900000000, -2975230737500000, 0], ![-78389062500, -1093750, 0]]], ![![![1955160564875854094952, -11822224796386560, -42533040908822903249], ![1507051491735406790300, 106400023167479040, 0]], ![![-8117082065139246443520, -882719337363840, 0], ![-23257201680, -324504, 0]]]]
 g := ![![![![-162251, 0, -1], ![546875, 0, 0]], ![![-4635, 0, 0], ![15625, 0, 0]]], ![![![-10, 0, 0], ![35, 0, 0]], ![![-85057, -1339117, 16], ![284351, 4514172, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_1 : J0 ^ 6*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![546875, 0, 0], ![162252, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR61_J0_6J1_1]
 rfl
def MulR62_J0_6J1_2 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![15625, 0, 0], ![6002, 0, 1]] ![![1225, 0, 0], ![27, 0, 1]]
  ![![19140625, 0, 0], ![-8040873, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![19140625, 0, 0], ![421875, 0, 15625]], ![![7352450, 0, 1225], ![162025, 13, 6007]]]
 hmul := by decide
 f := ![![![![38794924004059625194563, 1848711134992312500000, -925054510480907504894], ![854316647836023652350, -566167792486358562500000, 0]], ![![23899588646828125000, 63103195312500, 0], ![1829078125000, -38281250, 0]]], ![![![-16297537669814592293499, -776633545151166212640, 388610394741767636719], ![-358893801379797732990, 237844026309128538567840, 0]], ![![-10040087879125514760, -26509310923860, 0], ![-768385823880, 16081746, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![6564, 0, 0], ![15625, 0, 0]]], ![![![515, 0, 0], ![1225, 0, 0]], ![![2417170, -30956419, -8], ![5753101, -73688953, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_2 : J0 ^ 6*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![19140625, 0, 0], ![-8040873, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR62_J0_6J1_2]
 rfl

lemma PowJ0_7J1_0 : J0 ^ 7*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![78125, 0, 0], ![6002, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
def MulR71_J0_7J1_1 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![78125, 0, 0], ![6002, 0, 1]] ![![35, 0, 0], ![27, 0, 1]]
  ![![2734375, 0, 0], ![162252, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![2734375, 0, 0], ![2109375, 0, 78125]], ![![210070, 0, 35], ![162025, 13, 6007]]]
 hmul := by decide
 f := ![![![![3893755135392106701003, -4851760375000000, -84715373652415351299], ![3001333522340984730760, 43665843375000000, 0]], ![![-80821683956463064453125, -1811309937500000, 0], ![-391945312500, -5468750, 0]]], ![![![231047152723251235251, -287893147196160, -5026830191854334384], ![178092751238169400545, 2591038324765440, 0]], ![![-4795786922168336506020, -107479281363840, 0], ![-23257201680, -324504, 0]]]]
 g := ![![![![-162251, 0, -1], ![2734375, 0, 0]], ![![-4635, 0, 0], ![78125, 0, 0]]], ![![![-2, 0, 0], ![35, 0, 0]], ![![-17885, -1955005, 24], ![284351, 32951672, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_1 : J0 ^ 7*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2734375, 0, 0], ![162252, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR71_J0_7J1_1]
 rfl
def MulR72_J0_7J1_2 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![78125, 0, 0], ![6002, 0, 1]] ![![1225, 0, 0], ![27, 0, 1]]
  ![![95703125, 0, 0], ![30240377, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![95703125, 0, 0], ![2109375, 0, 78125]], ![![7352450, 0, 1225], ![162025, 13, 6007]]]
 hmul := by decide
 f := ![![![![1950129332281436189380928, 92972600960845976562500, -46521582027154358686649], ![42944465624140100208475, -28472859118637399101562500, 0]], ![![17556152038729746093750, 3173450546875000, 0], ![9145390625000, -191406250, 0]]], ![![![616203976693017082444499, 29377583059346751427220, -14699939830988507887047], ![13569638719086100178950, -8996884835427084278916820, 0]], ![![5547411919104063978990, 1002750337863640, 0], ![2889770426120, -60480754, 0]]]]
 g := ![![![![-30240376, 0, -1], ![95703125, 0, 0]], ![![-24686, 0, 0], ![78125, 0, 0]]], ![![![-387, 0, 0], ![1225, 0, 0]], ![![-19962251, -55340623, 3], ![63174976, 175139172, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_2 : J0 ^ 7*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![95703125, 0, 0], ![30240377, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR72_J0_7J1_2]
 rfl

lemma PowJ0_8J1_0 : J0 ^ 8*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![390625, 0, 0], ![162252, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
def MulR81_J0_8J1_1 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![390625, 0, 0], ![162252, 0, 1]] ![![35, 0, 0], ![27, 0, 1]]
  ![![13671875, 0, 0], ![2896627, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![13671875, 0, 0], ![10546875, 0, 390625]], ![![5678820, 0, 35], ![4380775, 13, 162257]]]
 hmul := by decide
 f := ![![![![138762565738426202993331822, -35814206047812500000, -3054564516803416004619602], ![106958134583448687566152615, 322327854430312500000, 0]], ![![-532721429014320340224609375, -2463875885625000000, 0], ![-53229257812500, -27343750, 0]]], ![![![29399288283955220267736918, -7587868980784053280, -647163176419820141071599], ![22660960585439175059652175, 68290820827056479520, 0]], ![![-112866397239695629468802895, -522015408636363840, 0], ![-11277553764180, -5793254, 0]]]]
 g := ![![![![-2896626, 0, -1], ![13671875, 0, 0]], ![![-82760, 0, 0], ![390625, 0, 0]]], ![![![-7, 0, 0], ![35, 0, 0]], ![![-1832401, -37106017, 25], ![8643726, 175139172, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_1 : J0 ^ 8*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13671875, 0, 0], ![2896627, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR81_J0_8J1_1]
 rfl
def MulR82_J0_8J1_2 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![390625, 0, 0], ![162252, 0, 1]] ![![1225, 0, 0], ![27, 0, 1]]
  ![![478515625, 0, 0], ![125943502, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![478515625, 0, 0], ![10546875, 0, 390625]], ![![198758700, 0, 1225], ![4380775, 13, 162257]]]
 hmul := by decide
 f := ![![![![69074361024986918098509293071, 3427924166576653238085937500, -1715221502887800410831430065], ![1521055123405517541427689950, -1049801776562568271835742187500, 0]], ![![6930098545909683181201171875, 4312279606250000000, 0], ![1242016015625000, -957031250, 0]]], ![![![18180110473715799707717885578, 902216670833047636102128840, -451439809889996166409715533], ![400335953453417629340387180, -276303855586975598276610800040, 0]], ![![1823975716732287008498366490, 1134975676529488640, 0], ![326893916051120, -251887004, 0]]]]
 g := ![![![![-125943501, 0, -1], ![478515625, 0, 0]], ![![-102811, 0, 0], ![390625, 0, 0]]], ![![![-322, 0, 0], ![1225, 0, 0]], ![![-92234671, -46095959, 0], ![350440601, 175139172, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_2 : J0 ^ 8*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![478515625, 0, 0], ![125943502, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR82_J0_8J1_2]
 rfl
