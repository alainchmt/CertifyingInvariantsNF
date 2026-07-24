import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_126635_1.RI3_1_126635_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![280, -58, 25]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-95, -14, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![0, 1, 3]]]
 hmul := by decide
 f := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![-54, -80, -9], ![165, -5, 0]], ![![0, 0, 0], ![23, -1, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, -2, -6], ![0, 9, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![8, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![0, 2, 0], ![0, 1, 3]]]
 hmul := by decide
 f := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![-27, -924, -39], ![1877, -29, 0]], ![![-99, 99, 0], ![23, -1, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, -1, -3], ![0, 9, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![16, 0, 0], ![8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![0, 8, 0]], ![![0, 2, 0], ![0, 1, 3]]]
 hmul := by decide
 f := ![![![![406, -56700, -1113], ![114233, -833, 0]], ![![-6615, 6615, 0], ![-660, 30, 0]]], ![![![203, -28260, -555], ![56935, -415, 0]], ![![-3297, 3297, 0], ![-329, 15, 0]]]]
 g := ![![![![-7, 8, 3], ![16, -16, 0]], ![![-4, -36, -12], ![8, 64, 0]]], ![![![-1, -9, -3], ![2, 16, 0]], ![![-4, -10, -3], ![8, 17, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![8, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![32, 0, 0], ![8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![0, 16, 0]], ![![16, 2, 0], ![0, 9, 3]]]
 hmul := by decide
 f := ![![![![-6060347, 12523974, 118821], ![-25137067, 89119, 0]], ![![12121506, -1347834, 0], ![1800, 60, 0]]], ![![![-1512018, 3124650, 29643], ![-6271536, 22236, 0]], ![![3024239, -336276, 0], ![449, 15, 0]]]]
 g := ![![![![-7, 26, 9], ![32, -96, 0]], ![![-4, -108, -36], ![16, 384, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, -63, -21], ![0, 225, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![8, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![64, 0, 0], ![8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![0, 32, 0]], ![![16, 2, 0], ![0, 9, 3]]]
 hmul := by decide
 f := ![![![![-28919915, 121462134, 567048], ![-243349557, 425289, 0]], ![![115681284, -12855476, 0], ![3600, 120, 0]]], ![![![-3607641, 15151902, 70737], ![-30356857, 53053, 0]], ![![14430767, -1603668, 0], ![449, 15, 0]]]]
 g := ![![![![-7, 62, 21], ![64, -448, 0]], ![![-4, -252, -84], ![32, 1792, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, -72, -24], ![0, 513, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![64, 0, 0], ![8, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![128, 0, 0], ![-56, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![128, 0, 0], ![0, 64, 0]], ![![16, 2, 0], ![0, 9, 3]]]
 hmul := by decide
 f := ![![![![-125504459, 1062601380, 2460864], ![-2127048409, 1845649, 0]], ![![1004038920, -111563880, 0], ![7200, 240, 0]]], ![![![54924169, -465023302, -1076943], ![930854309, -807705, 0]], ![![-439394773, 48823392, 0], ![-3151, -105, 0]]]]
 g := ![![![![57, 4454, -243], ![128, 10368, 0]], ![![28, -1980, 108], ![64, -4608, 0]]], ![![![57, 494, -27], ![130, 1152, 0]], ![![28, -275, 15], ![64, -639, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![128, 0, 0], ![-56, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![256, 0, 0], ![-56, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![256, 0, 0], ![0, 128, 0]], ![![-112, 2, 0], ![0, -55, 3]]]
 hmul := by decide
 f := ![![![![-91047288899, 36182556900, 41733051], ![-72396413591, 31299791, 0]], ![![-208108089840, -3783791760, 0], ![16320, 480, 0]]], ![![![19910189250, -7912388880, -9126171], ![15831622386, -6844626, 0]], ![![45509004203, 827438257, 0], ![-3569, -105, 0]]]]
 g := ![![![![57, 12374, -675], ![256, 57600, 0]], ![![28, -5500, 300], ![128, -25600, 0]]], ![![![0, -5500, 300], ![2, -25600, 0]], ![![56, 2364, -129], ![256, 11009, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![256, 0, 0], ![-56, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![512, 0, 0], ![-56, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![512, 0, 0], ![0, 256, 0]], ![![-112, 2, 0], ![0, -55, 3]]]
 hmul := by decide
 f := ![![![![-417480522179, 332466562864, 191358675], ![-665076644735, 143519007, 0]], ![![-1908482388960, -34699696416, 0], ![32640, 960, 0]]], ![![![45647257285, -36351843814, -20923131], ![72719379973, -15692345, 0]], ![![208673176363, 3794059569, 0], ![-3569, -105, 0]]]]
 g := ![![![![1, -3465, 189], ![0, -32256, 0]], ![![28, 1540, -84], ![256, 14336, 0]]], ![![![0, 770, -42], ![2, 7168, 0]], ![![0, -330, 18], ![0, -3071, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ08 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![512, 0, 0], ![-56, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![1024, 0, 0], ![456, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07
 hI2 := rfl
 M := ![![![1024, 0, 0], ![0, 512, 0]], ![![-112, 2, 0], ![0, -55, 3]]]
 hmul := by decide
 f := ![![![![103016513341, -164237242832, -47219034], ![328509899939, -35414275, 0]], ![![941865261120, 17124789696, 0], ![65280, 1920, 0]]], ![![![45876342813, -73139769648, -21028053], ![146295310334, -15771038, 0]], ![![419440846923, 7626182417, 0], ![29071, 855, 0]]]]
 g := ![![![![-455, 28790, 189], ![1024, -64512, 0]], ![![-228, -12796, -84], ![512, 28672, 0]]], ![![![-1, -3199, -21], ![2, 7168, 0]], ![![-228, 1370, 9], ![512, -3071, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ09 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![1024, 0, 0], ![456, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2048, 0, 0], ![456, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08
 hI2 := rfl
 M := ![![![2048, 0, 0], ![0, 1024, 0]], ![![912, 2, 0], ![0, 457, 3]]]
 hmul := by decide
 f := ![![![![3584306116459765, 173534046789728, -325391921336493], ![-1252907661404321, 216945608977503, 99566408219098]], ![![189932750976, -9042648753792, 0], ![1835520, 3840, 0]]], ![![![798066208746567, 38638345696516, -72450367959708], ![-278967039855995, 48304177722375, 22169028912192]], ![![42289611083, -2013397342048, 0], ![408689, 855, 0]]]]
 g := ![![![![-455, 555254, 3645], ![2048, -2488320, 0]], ![![-228, -246780, -1620], ![1024, 1105920, 0]]], ![![![-456, 246779, 1620], ![2050, -1105920, 0]], ![![0, -110137, -723], ![0, 493569, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ010 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![2048, 0, 0], ![456, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4096, 0, 0], ![-1592, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09
 hI2 := rfl
 M := ![![![4096, 0, 0], ![0, 2048, 0]], ![![912, 2, 0], ![0, 457, 3]]]
 hmul := by decide
 f := ![![![![404983108687048285, 38784002856548040, -72721746360249750], ![-203897170164189789, 48483137378284965, 11249675478466408]], ![![23392730915072, -2020493436898560, 0], ![3671040, 7680, 0]]], ![![![-157405654391879387, -15074261663315400, 28264917298565511], ![79249150914952933, -18844045102872699, -4372435522372968]], ![![-9092102950709, 785309522317088, 0], ![-1426831, -2985, 0]]]]
 g := ![![![![4777, 51015412, -96195], ![12288, 131338240, 0]], ![![796, -770044, 1452], ![2048, -1982464, 0]]], ![![![1593, 11358148, -21417], ![4098, 29241344, 0]], ![![796, -171828, 324], ![2048, -442367, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ011 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![4096, 0, 0], ![-1592, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![8192, 0, 0], ![-1592, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010
 hI2 := rfl
 M := ![![![8192, 0, 0], ![0, 4096, 0]], ![![-3184, 2, 0], ![0, -1591, 3]]]
 hmul := by decide
 f := ![![![![34006375473972612741, 546171713436653256, -1024084219953159462], ![-8409522222533800275, 682736704862798853, 944620078802624490]], ![![135428060316160, -28449916298170880, 0], ![24115200, 15360, 0]]], ![![![-6608659444482101204, -106140769252950160, 199016324374775205], ![1634272035314846841, -132680249212076283, -183573589311343456]], ![![-26318533433141, 5528839972449681, 0], ![-4686449, -2985, 0]]]]
 g := ![![![![4777, 149581044, -282051], ![24576, 770187264, 0]], ![![796, -770044, 1452], ![4096, -3964928, 0]]], ![![![0, -58138322, 109626], ![2, -299352064, 0]], ![![1592, 299107, -564], ![8192, 1540097, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ012 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![8192, 0, 0], ![-1592, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![16384, 0, 0], ![-1592, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ011
 hI2 := rfl
 M := ![![![16384, 0, 0], ![0, 8192, 0]], ![![-3184, 2, 0], ![0, -1591, 3]]]
 hmul := by decide
 f := ![![![![67899825026235604245, 2173025363651244128, -4074446939022231660], ![-20309072782221510259, 2716325592481123209, 1886104581773384476]], ![![309167694537728, -113185312639755264, 0], ![48230400, 30720, 0]]], ![![![-6597686656503895352, -211148415190565412, 395905647648330405], ![1973390924784507192, -263939783487043239, -183268911622805338]], ![![-30041190416181, 10997984554849681, 0], ![-4686449, -2985, 0]]]]
 g := ![![![![-31839, -5521608437, 10411581], ![-327680, -56861114368, 0]], ![![796, 12263428, -23124], ![8192, 126287872, 0]]], ![![![6368, 1073049946, -2023350], ![65538, 11050188800, 0]], ![![0, -2381727, 4491], ![0, -24526847, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ013 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![16384, 0, 0], ![-1592, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![32768, 0, 0], ![-1592, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ012
 hI2 := rfl
 M := ![![![32768, 0, 0], ![0, 16384, 0]], ![![-3184, 2, 0], ![0, -1591, 3]]]
 hmul := by decide
 f := ![![![![-4444698302608422144379, -282384638827928611128, 529472781985872753612], ![1784855919826852903513, -352983650065222657863, -123463785065105095034]], ![![-20997296382441472, 14707982124282132480, 0], ![96460800, 61440, 0]]], ![![![215941105891217620864, 13719367894871305864, -25723891768813680921], ![-86715393249010111218, 17149348407263100681, 5998361299084829548]], ![![1020132097360075, -714572218204740207, 0], ![-4686449, -2985, 0]]]]
 g := ![![![![-35023, -24341942003, 45899325], ![-720896, -501343027200, 0]], ![![796, 25296900, -47700], ![16384, 521011200, 0]]], ![![![4776, 2365260147, -4459950], ![98306, 48714547200, 0]], ![![0, -2456504, 4632], ![0, -50593791, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ014 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![32768, 0, 0], ![-1592, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![65536, 0, 0], ![-1592, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ013
 hI2 := rfl
 M := ![![![65536, 0, 0], ![0, 32768, 0]], ![![-3184, 2, 0], ![0, -1591, 3]]]
 hmul := by decide
 f := ![![![![-17904155185289029270939, -2241709895902176012600, 4203212342739445393542], ![10778269157253948708573, -2802148688138877681603, -497337529832824741240]], ![![-84622687732920320, 116757505323051479040, 0], ![192921600, 122880, 0]]], ![![![434927501043012587220, 54455587152708542400, -102104378657467627416], ![-261825571864186336749, 68069758883936076744, 12081316699199696530]], ![![2055653211586763, -2836271775609682543, 0], ![-4686449, -2985, 0]]]]
 g := ![![![![-17511, -50245967614, 94744125], ![-720896, -2069716992000, 0]], ![![796, 25296900, -47700], ![32768, 1042022400, 0]]], ![![![1592, 2441150849, -4603050], ![65538, 100555161600, 0]], ![![0, -1228252, 2316], ![0, -50593791, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ015 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![65536, 0, 0], ![-1592, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![280, -58, 25]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ014
 hI2 := rfl
 M := ![![![131072, 0, 0], ![0, 65536, 0]], ![![-3184, 2, 0], ![0, -1591, 3]]]
 hmul := by decide
 f := ![![![![-36980981113708936117, -8996933961984351692, 16869263796676994354], ![36453555472514142589, -11246190164801842498, -1027249360123552486]], ![![-170807771326263, 468593885607652095, 0], ![824192, 525, 0]]]]
 g := ![![![![5591, 1240, 167]], ![![-6012, 4000, 1860]]], ![![![-136, -30, -4]], ![![144, -97, -45]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow17 : J0 ^ 17 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ015, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-6239, 1330, -588])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     

lemma PowJ0_4 : J0 ^ 4 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     

lemma PowJ0_5 : J0 ^ 5 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     

lemma PowJ0_6 : J0 ^ 6 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64, 0, 0], ![8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     

lemma PowJ0_7 : J0 ^ 7 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![128, 0, 0], ![-56, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     

lemma PowJ0_8 : J0 ^ 8 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![256, 0, 0], ![-56, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     

lemma PowJ0_9 : J0 ^ 9 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![512, 0, 0], ![-56, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07]
 rfl     

lemma PowJ0_10 : J0 ^ 10 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1024, 0, 0], ![456, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ08]
 rfl     

lemma PowJ0_11 : J0 ^ 11 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2048, 0, 0], ![456, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ09]
 rfl     

lemma PowJ0_12 : J0 ^ 12 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4096, 0, 0], ![-1592, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ010]
 rfl     

lemma PowJ0_13 : J0 ^ 13 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8192, 0, 0], ![-1592, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ011]
 rfl     

lemma PowJ0_14 : J0 ^ 14 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16384, 0, 0], ![-1592, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ012]
 rfl     

lemma PowJ0_15 : J0 ^ 15 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32768, 0, 0], ![-1592, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ013]
 rfl     

lemma PowJ0_16 : J0 ^ 16 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![65536, 0, 0], ![-1592, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ014]
 rfl     
