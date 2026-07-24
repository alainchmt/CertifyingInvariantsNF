import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_817516_2.RI3_1_817516_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![262, -15, 14]

def alpha1 := B.equivFun.symm ![43, -2, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![4, -3, -2]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![9, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![4, 5, 7]]]
 hmul := by decide
 f := ![![![![11634, 11634, 16387], ![7758, 7317, 0]], ![![0, 0, 0], ![-43074, 18, 0]]], ![![![646, 646, 910], ![432, 407, 0]], ![![0, 0, 0], ![-2394, 1, 0]]]]
 g := ![![![![3, 3, 7], ![9, -9, 0]], ![![0, 0, 0], ![3, 0, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![27, 0, 0], ![-8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![3, 3, 0], ![4, 5, 7]]]
 hmul := by decide
 f := ![![![![0, -2460, -8633], ![2774, 10720, -20]], ![![12798, 21951, 0], ![-129222, 54, 0]]], ![![![0, 771, 3358], ![244, -3649, 8]], ![![-4029, -6910, 0], ![40680, -17, 0]]]]
 g := ![![![![277, -497, 700], ![-81, -2700, 0]], ![![85, -149, 210], ![-18, -810, 0]]], ![![![31, -50, 70], ![3, -270, 0]], ![![42, -65, 91], ![10, -350, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![27, 0, 0], ![-8, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![81, 0, 0], ![19, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0, 0], ![27, 27, 0]], ![![-24, 3, 0], ![-5, -4, 7]]]
 hmul := by decide
 f := ![![![![263713187, 263713187, 578345047], ![175808793, -248241996, 0]], ![![251207892, 3352752, 0], ![198207, 162, 0]]], ![![![60230762, 60230762, 132091092], ![40153842, -56697220, 0]], ![![57374616, 765752, 0], ![45270, 37, 0]]]]
 g := ![![![![1769, 14072, 4480], ![648, -51840, 0]], ![![567, 4617, 1470], ![270, -17010, 0]]], ![![![-533, -4178, -1330], ![-159, 15390, 0]], ![![-111, -858, -273], ![-26, 3160, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![81, 0, 0], ![19, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![243, 0, 0], ![100, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![243, 0, 0], ![81, 81, 0]], ![![57, 3, 0], ![22, 23, 7]]]
 hmul := by decide
 f := ![![![![120288276921, 120288276921, 255908358475], ![80192184615, -109871646885, 0]], ![![-159202963890, 5309541738, 0], ![-1110510, 486, 0]]], ![![![49253949554, 49253949554, 104785750545], ![32835966372, -44988694590, 0]], ![![-65188187520, 2174076374, 0], ![-454716, 199, 0]]]]
 g := ![![![![93917, 4003589, 272104], ![55161, -9445896, 0]], ![![31167, 1328625, 90300], ![18306, -3134700, 0]]], ![![![21947, 938894, 63812], ![13125, -2215188, 0]], ![![8442, 360788, 24521], ![5023, -851228, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![243, 0, 0], ![100, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![729, 0, 0], ![343, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![729, 0, 0], ![243, 243, 0]], ![![300, 3, 0], ![103, 104, 7]]]
 hmul := by decide
 f := ![![![![3831320451756, 3831320451756, 8133175307320], ![2554213634505, -3484942758918, 0]], ![![-2908899720063, -57007085580, 0], ![-2622942, 1458, 0]]], ![![![1800038846881, 1800038846881, 3821145134170], ![1200025897923, -1637302967528, 0]], ![![-1366665243414, -26783186080, 0], ![-1232316, 685, 0]]]]
 g := ![![![![671723, 102235454, 2068360], ![456354, -215404920, 0]], ![![223264, 34030621, 688485], ![152604, -71700795, 0]]], ![![![276290, 42071612, 851165], ![188085, -88642755, 0]], ![![94654, 14424305, 291823], ![64639, -30391280, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![729, 0, 0], ![343, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![2187, 0, 0], ![343, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![2187, 0, 0], ![729, 729, 0]], ![![1029, 3, 0], ![346, 347, 7]]]
 hmul := by decide
 f := ![![![![1969292728021389, 1969292728021389, 4188035546935261], ![1312861818680928, -1794767414202117, 0]], ![![-1300810080098277, -25506022577868, 0], ![-1491534, 4374, 0]]], ![![![308406788610061, 308406788610061, 655879430841558], ![205604525740044, -281074746603161, 0]], ![![-203717128330527, -3994444503616, 0], ![-233586, 685, 0]]]]
 g := ![![![![7836986, 933850820, 18892951], ![1657746, -5902697691, 0]], ![![2610570, 311067588, 6293280], ![551853, -1966200480, 0]]], ![![![3687231, 439382967, 8889258], ![780762, -2777258178, 0]], ![![1238952, 147639464, 2986928], ![262441, -933201647, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![2187, 0, 0], ![343, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![6561, 0, 0], ![343, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![6561, 0, 0], ![2187, 2187, 0]], ![![1029, 3, 0], ![346, 347, 7]]]
 hmul := by decide
 f := ![![![![-2295014467066214553, -2295014467066214553, -4905384036957243497], ![-1530009644710809699, 2102308388519639337, 0]], ![![4480546033653929190, -688255746875892, 0], ![-4474602, 13122, 0]]], ![![![-119805794852384707, -119805794852384707, -256073955976028456], ![-79870529901589803, 109746030417578457, 0]], ![![233896294179273810, -35928761234170, 0], ![-233586, 685, 0]]]]
 g := ![![![![70568422, 8168678647, 165262300], ![4940433, -154897992900, 0]], ![![23518633, 2722424629, 55077960], ![1648998, -51623785080, 0]]], ![![![11067686, 1281141002, 25919040], ![774201, -24293545920, 0]], ![![3720743, 430708026, 8713747], ![262441, -8167270580, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![6561, 0, 0], ![343, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![262, -15, 14]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![19683, 0, 0], ![6561, 6561, 0]], ![![1029, 3, 0], ![346, 347, 7]]]
 hmul := by decide
 f := ![![![![-568721388964569556, -568721388964569556, -1215560761756795447], ![-379147592643046368, 520954699494280020, 0]], ![![3331176698496179370, -190953085414782, 0], ![-183784, 539, 0]]]]
 g := ![![![![-1330, 82, 133]], ![![-8031, -600, 147]]], ![![![-73, 4, 7]], ![![-424, -33, 7]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow9 : J0 ^ 9 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![45, 0, 0], ![1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![45, 0, 0], ![1, 1, 0]] ![![45, 0, 0], ![1, 1, 0]]
  ![![2025, 0, 0], ![991, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![2025, 0, 0], ![45, 45, 0]], ![![45, 45, 0], ![4, 5, 7]]]
 hmul := by decide
 f := ![![![![-61591915, -51916465, 141371545], ![6779511124, -216594057, 1968045]], ![![-792678148, -691881750, 787218], ![866970, 496125, 0]]], ![![![-30141153, -25406295, 69182792], ![3317680122, -105994306, 963100]], ![![-387911800, -338585208, 385240], ![424266, 242788, 0]]]]
 g := ![![![![209495, 93710270, 659932], ![149850, -190908900, 0]], ![![4275, 2080440, 14651], ![4095, -4238325, 0]]], ![![![4275, 2080440, 14651], ![4095, -4238325, 0]], ![![51, 184883, 1302], ![1036, -376649, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![2025, 0, 0], ![991, 1, 0]] ![![45, 0, 0], ![1, 1, 0]]
  ![![43, -2, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![91125, 0, 0], ![2025, 2025, 0]], ![![44595, 45, 0], ![994, 995, 7]]]
 hmul := by decide
 f := ![![![![760042616645859, 760042616645859, 1331004282738291], ![33779671850952, -8556454861995162, 0]], ![![-388985656291848, -55833412272, 0], ![-1117489197, -57266, 0]]]]
 g := ![![![![1907, 94, 28]], ![![-59, 47, 14]]], ![![![931, 47, 14]], ![![-30, 23, 7]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1228, -68, 65])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![45, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2025, 0, 0], ![991, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![1, 1, 0]] ![![45, 0, 0], ![1, 1, 0]]
  ![![135, 0, 0], ![46, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![135, 0, 0], ![3, 3, 0]], ![![45, 45, 0], ![4, 5, 7]]]
 hmul := by decide
 f := ![![![![14205, 14205, 16387], ![675, 109755, 0]], ![![0, 0, 0], ![-646110, 270, 0]]], ![![![4787, 4787, 5523], ![255, 36992, 0]], ![![0, 0, 0], ![-217764, 91, 0]]]]
 g := ![![![![21302, 405692, 57967], ![10395, -1117935, 0]], ![![453, 8916, 1274], ![273, -24570, 0]]], ![![![7025, 133745, 19110], ![3420, -368550, 0]], ![![603, 11855, 1694], ![361, -32669, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![135, 0, 0], ![46, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![1, 1, 0]] ![![2025, 0, 0], ![991, 1, 0]]
  ![![6075, 0, 0], ![3016, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![6075, 0, 0], ![2973, 3, 0]], ![![2025, 2025, 0], ![994, 995, 7]]]
 hmul := by decide
 f := ![![![![-1479476911180, -660485187787855, -4651307805368], ![-1050195952125, 1345556882451600, 0]], ![![0, 0, 0], ![43096050, 12150, 0]]], ![![![-734380644553, -327850698052593, -2308809552497], ![-521294773425, 667905611416862, 0]], ![![0, 0, 0], ![21391956, 6031, 0]]]]
 g := ![![![![23768745, 32490402720, 75333832], ![17155800, -65379004200, 0]], ![![11632059, 15900238374, 36867068], ![8395653, -31995348300, 0]]], ![![![7920799, 10828004839, 25106340], ![5718600, -21788716500, 0]], ![![3886226, 5315078854, 12323801], ![2810701, -10695298724, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6075, 0, 0], ![3016, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![9, 0, 0], ![1, 1, 0]] ![![45, 0, 0], ![1, 1, 0]]
  ![![405, 0, 0], ![181, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![405, 0, 0], ![9, 9, 0]], ![![45, 45, 0], ![4, 5, 7]]]
 hmul := by decide
 f := ![![![![-1432151, -1385309, 1609571], ![139325653, 58928023, 22605]], ![![-7089056, -13877169, 1810], ![967878, 22680, 0]]], ![![![-639611, -618689, 718798], ![62222516, 26317819, 10095]], ![![-3166008, -6197610, 808], ![432267, 10129, 0]]]]
 g := ![![![![47943, 3784068, 143962], ![30780, -8329230, 0]], ![![999, 83718, 3185], ![819, -184275, 0]]], ![![![5176, 418591, 15925], ![3690, -921375, 0]], ![![324, 37166, 1414], ![631, -81809, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![405, 0, 0], ![181, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![9, 0, 0], ![1, 1, 0]] ![![2025, 0, 0], ![991, 1, 0]]
  ![![18225, 0, 0], ![9091, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![18225, 0, 0], ![8919, 9, 0]], ![![2025, 2025, 0], ![994, 995, 7]]]
 hmul := by decide
 f := ![![![![11839569246210, 5285557389841635, 37222264477132], ![8404232352975, -10767869219466450, 0]], ![![0, 0, 0], ![-1034633250, -291600, 0]]], ![![![5905736302880, 2636507081462425, 18566965911795], ![4192144078770, -5371157922520481, 0]], ![![0, 0, 0], ![-516088974, -145454, 0]]]]
 g := ![![![![-44360806, -183111998791, -140948318], ![-32167125, 366969013650, 0]], ![![-21716324, -89611829531, -68977657], ![-15728166, 179588256975, 0]]], ![![![-4929679, -20341777294, -15657845], ![-3570075, 40766317875, 0]], ![![-2426261, -9985048213, -7685874], ![-1739474, 20010721951, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![18225, 0, 0], ![9091, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![27, 0, 0], ![-8, 1, 0]] ![![45, 0, 0], ![1, 1, 0]]
  ![![1215, 0, 0], ![586, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![1215, 0, 0], ![27, 27, 0]], ![![-360, 45, 0], ![-5, -4, 7]]]
 hmul := by decide
 f := ![![![![-130325411804, -130325411804, -234949871513], ![-5792240520, 1509978221235, 0]], ![![-100441005210, 251993430, 0], ![-166428270, 68040, 0]]], ![![![-62843129749, -62843129749, -113293217765], ![-2793027951, 728114002945, 0]], ![![-48432819318, 121511650, 0], ![-80251986, 32809, 0]]]]
 g := ![![![![-159565, -41797705, -496748], ![-110565, 86221260, 0]], ![![-3551, -924728, -10990], ![-2403, 1907550, 0]]], ![![![46684, 12391354, 147266], ![34065, -25561170, 0]], ![![573, 171398, 2037], ![622, -353564, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1215, 0, 0], ![586, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![27, 0, 0], ![-8, 1, 0]] ![![2025, 0, 0], ![991, 1, 0]]
  ![![54675, 0, 0], ![9091, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![54675, 0, 0], ![26757, 27, 0]], ![![-16200, 2025, 0], ![-7925, 986, 7]]]
 hmul := by decide
 f := ![![![![20781923459782350, 9277706464944318300, 65336012324037007], ![14751897586959600, -18900775018463820300, 0]], ![![0, 0, 0], ![682949525625, -15637050, 0]]], ![![![3455467158110707, 1542629586440949993, 10863597167248266], ![2452838291423313, -3142683470350694270, 0]], ![![0, 0, 0], ![113555882400, -2600015, 0]]]]
 g := ![![![![2190674107, 6887774683927, 5301783907], ![490270725, -41410719302175, 0]], ![![1072080672, 3370757736444, 2594601296], ![239913927, -20265689408400, 0]]], ![![![-649100652, -2040833072022, -1570907359], ![-145214775, 12269908550475, 0]], ![![-317539721, -998370474745, -768483982], ![-71030933, 6002408816551, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![54675, 0, 0], ![9091, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![19, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![81, 0, 0], ![19, 1, 0]] ![![45, 0, 0], ![1, 1, 0]]
  ![![3645, 0, 0], ![1801, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![3645, 0, 0], ![81, 81, 0]], ![![855, 45, 0], ![22, 23, 7]]]
 hmul := by decide
 f := ![![![![2171016102103, 2171016102103, 3750137160217], ![96489604575, -24106930908570, 0]], ![![-2412760547250, -1958381955, 0], ![-466217370, 204120, 0]]], ![![![1072627890649, 1072627890649, 1852819842244], ![47672350713, -11910444342366, 0]], ![![-1192065896670, -967572329, 0], ![-230342718, 100849, 0]]]]
 g := ![![![![-1002624, -816262899, -3167318], ![-718065, 1649267730, 0]], ![![-22980, -18126588, -70336], ![-14499, 36624960, 0]]], ![![![-235572, -191462082, -742924], ![-167625, 386851140, 0]], ![![-7307, -4923116, -19103], ![-1781, 9947206, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3645, 0, 0], ![1801, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![81, 0, 0], ![19, 1, 0]] ![![2025, 0, 0], ![991, 1, 0]]
  ![![164025, 0, 0], ![-45584, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![164025, 0, 0], ![80271, 81, 0]], ![![38475, 2025, 0], ![18832, 1013, 7]]]
 hmul := by decide
 f := ![![![![75149686626677389, 33549191718764627404, 236262099059568232], ![53344459834965450, -68347250035945867350, 0]], ![![0, 0, 0], ![-3118312408050, -852930000, 0]]], ![![![-20884769117888217, -9323620025441360419, -65659347519020185], ![-14824901837661321, 18994311232916274892, 0]], ![![0, 0, 0], ![866606869608, 237036865, 0]]]]
 g := ![![![![30012600535, -504199346803715, 77431285582], ![-11414663775, -1814380945369650, 0]], ![![14687676614, -246746442576409, 37893532355], ![-5586035319, -887926663504125, 0]]], ![![![7040025170, -118268902765630, 18162881891], ![-2677378050, -425595243167325, 0]], ![![3445803881, -57887977745494, 8890016548], ![-1310513156, -208312137755099, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![164025, 0, 0], ![-45584, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![243, 0, 0], ![100, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![243, 0, 0], ![100, 1, 0]] ![![45, 0, 0], ![1, 1, 0]]
  ![![10935, 0, 0], ![-1844, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![10935, 0, 0], ![243, 243, 0]], ![![4500, 45, 0], ![103, 104, 7]]]
 hmul := by decide
 f := ![![![![-161952134217050959, -161952134217050959, -282961829760079358], ![-7197872631868890, 1819035249862463190, 0]], ![![99247837158332325, 27455294247570, 0], ![-1101045150, 612360, 0]]], ![![![27312298044145420, 27312298044145420, 47719888761492808], ![1213879913073147, -306769856027123658, 0]], ![![-16737578185121511, -4630177817690, 0], ![185684946, -103271, 0]]]]
 g := ![![![![-1305789, 833004606, -3167318], ![306180, 4947803190, 0]], ![![-28259, 18498367, -70336], ![11178, 109874880, 0]]], ![![![-536470, 342797870, -1303414], ![131265, 2036118870, 0]], ![![-10605, 7840818, -29813], ![12880, 46572166, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10935, 0, 0], ![-1844, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![243, 0, 0], ![100, 1, 0]] ![![2025, 0, 0], ![991, 1, 0]]
  ![![492075, 0, 0], ![-45584, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![492075, 0, 0], ![240813, 243, 0]], ![![202500, 2025, 0], ![99103, 1094, 7]]]
 hmul := by decide
 f := ![![![![-4864170156506923096666187697, -2171519062844507423154515854542, -15292399772595407013318546668], ![-3452795895280428746642323350, 4423872791332101551979762536400, 0]], ![![56310090668873247546450, 3102657231386012850, 0], ![-10598509164150, -2558790000, 0]]], ![![![450598777048890705133813312, 201161514209601771694608759811, 1416631493957157838443287386], ![319854272723482696534428807, -409811253606639790136788721346, 0]], ![![-5216359044710635832274, -287418718729282734, 0], ![981806785998, 237036865, 0]]]]
 g := ![![![![219549609819, -3374039469736341, 518160555682], ![-27194524875, -36424836491031450, 0]], ![![107443771887, -1651196592872610, 253578819032], ![-13308660207, -17825685339310200, 0]]], ![![![90349620890, -1388493551571835, 213234787766], ![-11191259700, -14989644027136350, 0]], ![![44216902195, -679525312842727, 104356578179], ![-5476748075, -7335894743918774, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![492075, 0, 0], ![-45584, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl

lemma PowJ0_6J1_0 : J0 ^ 6*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![729, 0, 0], ![343, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
def MulR61_J0_6J1_1 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) J1
  ![![729, 0, 0], ![343, 1, 0]] ![![45, 0, 0], ![1, 1, 0]]
  ![![32805, 0, 0], ![-12779, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![32805, 0, 0], ![729, 729, 0]], ![![15435, 45, 0], ![346, 347, 7]]]
 hmul := by decide
 f := ![![![![-21700108206248786400, -21700108206248786400, -37984022508893692133], ![-964449253611057150, 244182933837704209995, 0]], ![![11567664929167105500, 1101683977533270, 0], ![-624672810, 1837080, 0]]], ![![![8453235634701565868, 8453235634701565868, 14796603296615162526], ![375699361542291858, -95120994701236800047, 0]], ![![-4506161741689605900, -429158885686214, 0], ![243340098, -715631, 0]]]]
 g := ![![![![325074309, -1679347651476, 920118472], ![-177803100, -4312069496280, 0]], ![![7229129, -37315821280, 20445425], ![-3935871, -95816023875, 0]]], ![![![152951817, -790145553858, 432922581], ![-83652705, -2028860752815, 0]], ![![3435507, -17710934359, 9703862], ![-1856762, -45476456129, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_1 : J0 ^ 6*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32805, 0, 0], ![-12779, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR61_J0_6J1_1]
 rfl
def MulR62_J0_6J1_2 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![729, 0, 0], ![343, 1, 0]] ![![2025, 0, 0], ![991, 1, 0]]
  ![![1476225, 0, 0], ![-45584, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1476225, 0, 0], ![722439, 729, 0]], ![![694575, 2025, 0], ![339916, 1337, 7]]]
 hmul := by decide
 f := ![![![![172176663901740263148744704073, 76865096365601674185181316609103, 541303920549171454237752045157], ![122218355699864827143499910925, -156591491301635539238728540001100, 0]], ![![-1743317754700118915205000, -32061608252945488125, 0], ![10581577847550, 1889568000, 0]]], ![![![-5316603633935089481493531108, -2373499645070066817245399851052, -16714799356882810190037726395], ![-3773952516691229873286659082, 4835352671095491455281887814298, 0]], ![![53831508287509177109325, 990023032649143675, 0], ![-326746110432, -58347536, 0]]]]
 g := ![![![![-491831063723, 7482220932447322, -1149065323868], ![20256759450, 242325565389576900, 0]], ![![-240693634889, 3661669586735029, -562332706768], ![9912851604, 118589942864084400, 0]]], ![![![-231410237169, 3520441356533016, -540643897584], ![9530510625, 114016005387277200, 0]], ![![-113249144416, 1722858350954575, -264584113045], ![4664917918, 55797954611407876, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_2 : J0 ^ 6*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1476225, 0, 0], ![-45584, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR62_J0_6J1_2]
 rfl

lemma PowJ0_7J1_0 : J0 ^ 7*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2187, 0, 0], ![343, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
def MulR71_J0_7J1_1 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![2187, 0, 0], ![343, 1, 0]] ![![45, 0, 0], ![1, 1, 0]]
  ![![98415, 0, 0], ![-45584, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![98415, 0, 0], ![2187, 2187, 0]], ![![15435, 45, 0], ![346, 347, 7]]]
 hmul := by decide
 f := ![![![![656627486045603309, 656627486045603309, 1149023256658063927], ![29183443824249045, -7386550353093392055, 0]], ![![-1051019077228892460, -1347455545441020, 0], ![-1874018430, 5511240, 0]]], ![![![-304138488987640479, -304138488987640479, -532207689318949623], ![-13517266177228449, 3421322303685780966, 0]], ![![486813849311478936, 624118091730304, 0], ![868012908, -2552711, 0]]]]
 g := ![![![![1100593996, -21872835997544, 3359071807], ![-731912355, -47226150269415, 0]], ![![24470105, -486052264039, 74644388], ![-16236288, -1049446777860, 0]]], ![![![172630295, -3430444564720, 526822842], ![-114751845, -7406752856490, 0]], ![![3897221, -76897152538, 11809308], ![-2512862, -166030435259, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_1 : J0 ^ 7*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![98415, 0, 0], ![-45584, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR71_J0_7J1_1]
 rfl
def MulR72_J0_7J1_2 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![2187, 0, 0], ![343, 1, 0]] ![![2025, 0, 0], ![991, 1, 0]]
  ![![4428675, 0, 0], ![1430641, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4428675, 0, 0], ![2167317, 2187, 0]], ![![694575, 2025, 0], ![339916, 1337, 7]]]
 hmul := by decide
 f := ![![![![82177140682384774593550284, 36686468970841976974227684774, 258355618155053883452475907], ![58332847104733475850092775, -74738589531547110318132185475, 0]], ![![-2496120839773819221375, -6658098463054341000, 0], ![31744733542650, 5668704000, 0]]], ![![![26546537213901018062167817, 11851211975666163512059426749, 83459304799633821596604584], ![18843866841798554277368856, -24143584600759698925542023059, 0]], ![![-806347899345365668440, -2150834856939439325, 0], ![10254831737118, 1831220464, 0]]]]
 g := ![![![![6683513324877, 3646699259329448397, 17842939833607], ![2982477892725, -11288654509657068675, 0]], ![![3270796362423, 1784631587582179683, 8732026355318], ![1459571707962, -5524472402733991950, 0]]], ![![![1048213952223, 571933170922922403, 2798412600522], ![467761084200, -1770465703373824050, 0]], ![![512982133650, 279896678782694678, 1369506845504], ![228916781443, -866442961287489599, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_2 : J0 ^ 7*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4428675, 0, 0], ![1430641, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR72_J0_7J1_2]
 rfl

lemma PowJ0_8J1_0 : J0 ^ 8*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6561, 0, 0], ![343, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
def MulR81_J0_8J1_1 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![6561, 0, 0], ![343, 1, 0]] ![![45, 0, 0], ![1, 1, 0]]
  ![![295245, 0, 0], ![-45584, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![295245, 0, 0], ![6561, 6561, 0]], ![![15435, 45, 0], ![346, 347, 7]]]
 hmul := by decide
 f := ![![![![11780250338532987612, 11780250338532987612, 20619557627079681277], ![523566681712577235, -132554211421544858655, 0]], ![![-56522764131215303925, -12773491588411830, 0], ![-5622055290, 16533720, 0]]], ![![![-1818802702190802918, -1818802702190802918, -3183540761221361121], ![-80835675652924548, 20465605652850674242, 0]], ![![8726788750904430510, 1972153422022108, 0], ![868012908, -2552711, 0]]]]
 g := ![![![![145940766588, -2288413429463772, 351437967727], ![-30282984405, -14822900397365445, 0]], ![![3243129511, -50853421636439, 7809700346], ![-672856794, -329396425522110, 0]]], ![![![7629588755, -119635085634850, 18372690364], ![-1583103645, -774920709502740, 0]], ![![171044705, -2681799066618, 411851286], ![-35383472, -17371004705009, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_1 : J0 ^ 8*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![295245, 0, 0], ![-45584, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR81_J0_8J1_1]
 rfl
def MulR82_J0_8J1_2 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![6561, 0, 0], ![343, 1, 0]] ![![2025, 0, 0], ![991, 1, 0]]
  ![![13286025, 0, 0], ![1430641, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![13286025, 0, 0], ![6501951, 6561, 0]], ![![694575, 2025, 0], ![339916, 1337, 7]]]
 hmul := by decide
 f := ![![![![4404606818383161348929788966641, 1966355485553938941981992811629151, 13847584714662501341358331468957], ![3126578193862544117911809225600, -4005908435312828142941479800024225, 0]], ![![-401376531743261613878247675, -818431248522655425600, 0], ![95234200627950, 17006112000, 0]]], ![![![474288664081311283362472253032, 211737427381697861802870764375506, 1491109814310496807857676074192], ![336670367153717206723496676552, -431356767711223662029696428786878, 0]], ![![-43220279785150448825559507, -88128788677373918816, 0], ![10254831737118, 1831220464, 0]]]]
 g := ![![![![-34262953817267, -16592949840432305162, -81187667150618], ![-4938335776350, 154094482207827073350, 0]], ![![-16767698280234, -8120302857616852644, -39731841047332], ![-2416727940939, 75411176207268447900, 0]]], ![![![-1791220733351, -867456453295837961, -4244378876276], ![-258160749750, 8055846265667834700, 0]], ![![-876600449690, -424521941740710607, -2077143994023], ![-126338241032, 3942426719027061226, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_2 : J0 ^ 8*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13286025, 0, 0], ![1430641, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR82_J0_8J1_2]
 rfl
