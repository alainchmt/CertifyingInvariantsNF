import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_780300_1.RI3_1_780300_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![784, -144, -64]

def alpha1 := B.equivFun.symm ![18, 0, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![1, -2, 1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![22, 0, 0], ![8, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![22, 0, 0], ![8, 0, 1]] ![![22, 0, 0], ![8, 0, 1]]
  ![![484, 0, 0], ![224, 2, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![484, 0, 0], ![176, 0, 22]], ![![176, 0, 22], ![64, 34, 16]]]
 hmul := by decide
 f := ![![![![101352738821, 1654544044, 12684575928], ![-263269540644, -355514060, 0]], ![![0, 0, 0], ![-21712572024, -21780, 0]]], ![![![46823290940, 764372014, 5860064526], ![-121626178490, -164241620, 0]], ![![0, 0, 0], ![-10030849579, -10062, 0]]]]
 g := ![![![![-3069695, 1948911472, 87006200], ![6632736, -4211100080, 0]], ![![-1116324, 708697539, 31638728], ![2412058, -1531314433, 0]]], ![![![-1116324, 708697539, 31638728], ![2412058, -1531314433, 0]], ![![-399496, 253622314, 11322584], ![863197, -548013064, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![484, 0, 0], ![224, 2, 0]] ![![22, 0, 0], ![8, 0, 1]]
  ![![5324, 0, 0], ![-520, 4, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![10648, 0, 0], ![3872, 0, 484]], ![![4928, 44, 0], ![2132, 16, 224]]]
 hmul := by decide
 f := ![![![![-4101156617256, -860540634760, -555987984118], ![12070244028535, 2366486745590, 0]], ![![-40132913099565, 358339333495, 0], ![-3003160589, -3993, 0]]], ![![![401590807301, 84265303796, 54443095998], ![-1181934633726, -231729585439, 0]], ![![3929869175298, -35089072590, 0], ![294073550, 391, 0]]]]
 g := ![![![![1369942, -10538, 0], ![14026078, 0, 0]], ![![498208, -3856, 1], ![5100876, -242, 0]]], ![![![634012, -4877, 0], ![6491298, 0, 0]], ![![274313, -2005, -4], ![2808539, 1076, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![5324, 0, 0], ![-520, 4, 0]] ![![22, 0, 0], ![8, 0, 1]]
  ![![117128, 0, 0], ![-13520, 0, 4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![117128, 0, 0], ![42592, 0, 5324]], ![![-11440, 88, 0], ![-3480, 32, -520]]]
 hmul := by decide
 f := ![![![![-823574312393478090679, -13783516407352858268, -103017967354611077590], ![2278245618494176154450, -612074358137852258, 0]], ![![1525266449273506511, -143389069690428840993, 0], ![3631383599426, 3821301, 0]]], ![![![95064584928965096151, 1591021291470960348, 11891289176237464730], ![-262976237637808735789, 70651298767363593, 0]], ![![-176060398830149990, 16551296207692421370, 0], ![-419167972340, -441090, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![154, 0, 0], ![1331, 0, 0]]], ![![![-60, 1191, 0], ![0, 10318, 0]], ![![25, -796, 0], ![-130, -6896, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![117128, 0, 0], ![-13520, 0, 4]] ![![22, 0, 0], ![8, 0, 1]]
  ![![2576816, 0, 0], ![-469552, 8, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![2576816, 0, 0], ![937024, 0, 117128]], ![![-297440, 0, 88], ![-108160, 136, -13488]]]
 hmul := by decide
 f := ![![![![-1069461447481672915036218959756, -44236213549771985709624892452, -11788715206907850832309393556], ![267213523122137903228813338078, 125826134901489603757500261327, -982723543993028875861019280]], ![![-290378818472877233987162, -86388527152275610940832, 0], ![478044490532210624, 6442040, 0]]], ![![![194879833378065390787717924863, 8060829070702723601535771154, 2148167996773943827056418128], ![-48692289923148862232958498930, -22928340485717678886688295016, 179074244294668967090561738]], ![![52913525675719659406412, 15741924888321374017968, 0], ![-87110415136134063, -1173884, 0]]]]
 g := ![![![![33135088792948785, 60515646808805912922968, -5155181688875392080], ![181839342528817072, 332098866470028307950432, 0]], ![![12049123197430586, 22005689748649820900188, -1874611523226829662], ![66123397283176926, 120763224170881657560833, 0]]], ![![![-3824759241831840, -6985277174160376235340, 595058879461745718], ![-20989583284705750, -38333931038477443851845, 0]], ![![-1390821569203415, -2540100839414204929570, 216385051235041152], ![-7632575886522615, -13939611554581845028638, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![2576816, 0, 0], ![-469552, 8, 0]] ![![22, 0, 0], ![8, 0, 1]]
  ![![784, -144, -64]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![56689952, 0, 0], ![20614528, 0, 2576816]], ![![-10330144, 176, 0], ![-3755056, 64, -469552]]]
 hmul := by decide
 f := ![![![![2832316679444898526288832413, 609694565748778169370102472, 384748465631929451522759952], ![-8464465822366627526094618521, -1676660055809139965767781798, 0]], ![![-72448421727380529023610161583, -1234341188662904701987410, 0], ![1225794843441, 27300, 0]]]]
 g := ![![![![7438, -1970, -1202]], ![![-12518, -2574, -99]]], ![![![-1356, 359, 219]], ![![2281, 469, 18]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 0, 0], ![2, -1, -2]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![6, 0, 0], ![2, -1, -2]] ![![6, 0, 0], ![2, -1, -2]]
  ![![18, 0, 0], ![-6, 0, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![36, 0, 0], ![12, -6, -12]], ![![12, -6, -12], ![684, 132, -3]]]
 hmul := by decide
 f := ![![![![-299535994886, 149774787392, 299444173590], ![898350480514, -5880964, 0]], ![![0, 0, 0], ![-13022076, 33, 0]]], ![![![99845722825, -49925124682, -99815115492], ![-299451333086, 1960331, 0]], ![![0, 0, 0], ![4340709, -11, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-25, 0, -2], ![8, 1, 0]]], ![![![-25, 0, -2], ![8, 1, 0]], ![![-147, 8, 64], ![-385, 2, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![18, 0, 0], ![-6, 0, 3]] ![![6, 0, 0], ![2, -1, -2]]
  ![![18, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![108, 0, 0], ![36, -18, -36]], ![![-36, 0, 18], ![-522, -198, 18]]]
 hmul := by decide
 f := ![![![![220585426638, -110293053490, -220561238726], ![-661758337081, 829310, 0]], ![![-145247507, 0, 0], ![152251, 0, 0]]]]
 g := ![![![![6, 0, 0]], ![![2, -1, -2]]], ![![![-2, 0, 1]], ![![-29, -11, 1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![341, 36, 19])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![2, -1, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![18, 0, 0], ![-6, 0, 3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![22, 0, 0], ![8, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![22, 0, 0], ![8, 0, 1]] ![![6, 0, 0], ![2, -1, -2]]
  ![![66, 0, 0], ![-20, 4, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![132, 0, 0], ![44, -22, -44]], ![![48, 0, 6], ![-154, -76, -14]]]
 hmul := by decide
 f := ![![![![-13412488931114, 6706242878194, 13412795263696], ![40237342333168, -56603299, 0]], ![![-8689751664, -792484, 0], ![99, 0, 0]]], ![![![4065090122954, -2032544580320, -4065182966873], ![-12195232646832, 17155469, 0]], ![![2633711300, 240188, 0], ![-30, 0, 0]]]]
 g := ![![![![83662, -3836, 6142], ![-25366, -17732, 0]], ![![28964, -1329, 2125], ![-8767, -6138, 0]]], ![![![30428, -1396, 2233], ![-9206, -6448, 0]], ![![-93889, 4302, -6895], ![28508, 19902, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![66, 0, 0], ![-20, 4, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![22, 0, 0], ![8, 0, 1]] ![![18, 0, 0], ![-6, 0, 3]]
  ![![396, 0, 0], ![12, 6, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![396, 0, 0], ![-132, 0, 66]], ![![144, 0, 18], ![-48, 102, 18]]]
 hmul := by decide
 f := ![![![![1430, 0, 268], ![-429, 0, 0]], ![![-4323, 0, 0], ![0, 0, 0]]], ![![![136327989, 0, 25561178], ![-41182464, -13442, 0]], ![![-411343537, -12314, 0], ![-11, 0, 0]]]]
 g := ![![![![-165, 359549, 899080], ![5478, -11867856, 0]], ![![53, -119719, -299364], ![-1760, 3951607, 0]]], ![![![-60, 130781, 327028], ![1992, -4316769, 0]], ![![103, -228769, -572052], ![-3403, 7551087, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![396, 0, 0], ![12, 6, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![484, 0, 0], ![224, 2, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![484, 0, 0], ![224, 2, 0]] ![![6, 0, 0], ![2, -1, -2]]
  ![![1452, 0, 0], ![-20, 4, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![2904, 0, 0], ![968, -484, -968]], ![![1344, 12, 0], ![-232, -220, -458]]]
 hmul := by decide
 f := ![![![![-15239514136321060058, 7618824221101202322, 15251446317325308291], ![45754729909373918924, 212892426940900, 0]], ![![3032761834260, 14894062885641300, 0], ![-5810741346, 2541, 0]]], ![![![209912896320331643, -104943598890412468, -210077253179193023], ![-630237144682998844, -2932433773417, 0]], ![![-41774023422, -205154564006100, 0], ![80038611, -35, 0]]]]
 g := ![![![![11681882, -686856, 687522], ![-161172, -49897980, 0]], ![![3907394, -229743, 229963], ![-53482, -16690014, 0]]], ![![![5406162, -317865, 318172], ![-74292, -23091858, 0]], ![![-927151, 54512, -54568], ![13439, 3960270, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1452, 0, 0], ![-20, 4, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![484, 0, 0], ![224, 2, 0]] ![![18, 0, 0], ![-6, 0, 3]]
  ![![4356, 0, 0], ![-1560, 12, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![8712, 0, 0], ![-2904, 0, 1452]], ![![4032, 36, 0], ![-324, -12, 672]]]
 hmul := by decide
 f := ![![![![10487402047671, -634543064171, -5266519237270], ![31599106990086, -1081517738778, 0]], ![![66309374678217, 67999338, 0], ![8349, 0, 0]]], ![![![-3755820304046, 227246911424, 1886081967008], ![-11316488781773, 387320545547, 0]], ![![-23747167757245, -24352389, 0], ![-2990, 0, 0]]]]
 g := ![![![![53042, -408, 0], ![148104, 0, 0]], ![![-17594, 222, -3], ![-49126, 242, 0]]], ![![![24572, -189, 0], ![68610, 0, 0]], ![![-1949, 97, -3], ![-5442, 229, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4356, 0, 0], ![-1560, 12, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5324, 0, 0], ![-520, 4, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![5324, 0, 0], ![-520, 4, 0]] ![![6, 0, 0], ![2, -1, -2]]
  ![![31944, 0, 0], ![2656, 9748, 1316]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![31944, 0, 0], ![10648, -5324, -10648]], ![![-3120, 24, 0], ![-2400, 528, 1020]]]
 hmul := by decide
 f := ![![![![-4592901394699, 2296481299998, 4592495011245], ![13777528201240, -6914986, 0]], ![![-1485396, 2296422216, 0], ![0, 0, 0]]], ![![![-380940957851, 190473017402, 380907249199], ![1142725328255, -573583, 0]], ![![-123504, 190483902, 0], ![0, 0, 0]]]]
 g := ![![![![254924315310968319439691, -3761100008060561832124, 55023130956494487501485], ![22314870364578770520520, -36664449418835567721634, 0]], ![![85026871569078210974232, -1254468672216396464650, 18352288927242769613093], ![7442850691803086046245, -12228976384945750795189, 0]]], ![![![-24898928316467628078100, 367353578561269928530, -5374210740792449859340], ![-2179534568607739320950, 3581084435702950415534, 0]], ![![-19158008042473740684447, 282653242061574590994, -4135084501848036587452], ![-1677001526472140061832, 2755397483296491938263, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![31944, 0, 0], ![2656, 9748, 1316]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![5324, 0, 0], ![-520, 4, 0]] ![![18, 0, 0], ![-6, 0, 3]]
  ![![95832, 0, 0], ![-40560, 0, 12]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![95832, 0, 0], ![-31944, 0, 15972]], ![![-9360, 72, 0], ![5160, -24, -1560]]]
 hmul := by decide
 f := ![![![![-512279546, 31159111, 256321246], ![-1545125676, -102615, 0]], ![![-1485396, 319360140, 0], ![0, 0, 0]]], ![![![216817538, -13187803, -108485578], ![653960039, 43431, 0]], ![![628680, -135166200, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![563, 0, 0], ![1331, 0, 0]]], ![![![-60, 1191, 0], ![0, 2814, 0]], ![![6640, 1293, -2], ![15842, 3055, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![95832, 0, 0], ![-40560, 0, 12]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![117128, 0, 0], ![-13520, 0, 4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![117128, 0, 0], ![-13520, 0, 4]] ![![6, 0, 0], ![2, -1, -2]]
  ![![351384, 0, 0], ![-29120, 16, 8]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![702768, 0, 0], ![234256, -117128, -234256]], ![![-81120, 0, 24], ![-27720, 13248, 27048]]]
 hmul := by decide
 f := ![![![![15201256320013838512964550987180, -7600628160732651791579283334088, -15201256304520876506724714653937], ![-45603768942049208455704839334346, 11171998728672378775591, 0]], ![![-5432612485916111952995220, -3905474370273636512, 0], ![658845, 0, 0]]], ![![![-1259763062743672395786002835106, 629881531431979321717763292638, 1259763061459735012120184896062], ![3779289186739953330543706949928, -925849221874571862029, 0]], ![![450213087647677184366300, 323655640730512508, 0], ![-54600, 0, 0]]]]
 g := ![![![![345804859402, -7455743810434, 20483476463], ![-28996632269, -89966674005208, 0]], ![![115274793574, -2485388235329, 6828210935], ![-9666090687, -29990584283660, 0]]], ![![![-39916001060, 860611094844, -2364392817], ![3347093894, 10384787860720, 0]], ![![-13640670155, 294100429264, -807994397], ![1143830772, 3548839407204, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![351384, 0, 0], ![-29120, 16, 8]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![117128, 0, 0], ![-13520, 0, 4]] ![![18, 0, 0], ![-6, 0, 3]]
  ![![2108304, 0, 0], ![-3120, 24, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![2108304, 0, 0], ![-702768, 0, 351384]], ![![-243360, 0, 72], ![81120, 408, -40584]]]
 hmul := by decide
 f := ![![![![148746821, -974196, -5364528], ![31957600, -4873916, -114784]], ![![0, 0, 0], ![0, 0, 0]]], ![![![1884669216114, -12343512018, -67970892244], ![404916621047, -61754001706, -1454365956]], ![![2438076, -2182000, 0], ![-47, 0, 0]]]]
 g := ![![![![2545771801, 151119682164440680, -5812295468616290], ![1720275919560, 102117381547213322268, 0]], ![![-848590557, -50373227433826792, 1937431824629016], ![-573425277238, -34039127213272104979, 0]]], ![![![-293856550, -17443635192817553, 670909045964538], ![-198570172932, -11787335210360161029, 0]], ![![97952205, 5814543008676897, -223636269593476], ![66190072285, 3929110347741698201, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2108304, 0, 0], ![-3120, 24, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2576816, 0, 0], ![-469552, 8, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![2576816, 0, 0], ![-469552, 8, 0]] ![![6, 0, 0], ![2, -1, -2]]
  ![![7730448, 0, 0], ![-2137424, 16, 8]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![15460896, 0, 0], ![5153632, -2576816, -5153632]], ![![-2817312, 48, 0], ![-941824, 469568, 939064]]]
 hmul := by decide
 f := ![![![![-44003174813080930338376869876192510913675, 22001850898843675683073653928067447272616, 43999734942673113057345883502978680081391], ![131999354875823075619261857336236857183475, -59820960263133582257882703508766865, 0]], ![![-320091056863473086116226763931, 10638021495161839119671860362016720424, 0], ![1080967449680627574766, -14977743, 0]]], ![![![12166622415890339527315870961311136377776, -6083384062037545448627944369903208904640, -12165671311689579307455230474911277377736], ![-36497055422415506644152287310860971736188, 16540148277236709250381276486138592, 0]], ![![88503319228762903057853779823, -2941351194170737126993685913202474770, 0], ![-298881225275192907293, 4141259, 0]]]]
 g := ![![![![1365143054414, -2311607690022012, 86519783046], ![-382237799196, -8360420323824888, 0]], ![![455048202277, -770536849920578, 28839963360], ![-127412921834, -2786810222227053, 0]]], ![![![-248758583373, 421225269522918, -15765788932], ![69652829622, 1523450678689557, 0]], ![![-83159731741, 140815272719757, -5270490706], ![23285120339, 509288350714908, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7730448, 0, 0], ![-2137424, 16, 8]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![2576816, 0, 0], ![-469552, 8, 0]] ![![18, 0, 0], ![-6, 0, 3]]
  ![![23191344, 0, 0], ![-10547760, 48, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![46382688, 0, 0], ![-15460896, 0, 7730448]], ![![-8451936, 144, 0], ![2821392, -48, -1408656]]]
 hmul := by decide
 f := ![![![![-35541966964735192799043005373376404, 232687771076435589838923128477811, 1288186754761048796238513973267868], ![-7674288375079737454267659314436074, 1164136617872302545381547878520384, 27416076743277040927004972319902]], ![![36357553775483596758223, -13327608168597077658765, 0], ![-45899535, 0, 0]]], ![![![16165002660990897373913979682080451, -105829777017200222964537503542494, -585886041119410768959322204253120], ![3490377787123120270165778588027835, -529466237598336605632031750281333, -12469229796671889512304256176380]], ![![-16535943385208501360022, 6061589717974150769220, 0], ![20875775, 0, 0]]]]
 g := ![![![![67427874272, -306846, 0], ![148253565438, 0, 0]], ![![-22475811594, 248778, -3], ![-49417533044, 322102, 0]]], ![![![-12286602184, 275658, -5], ![-27014533686, 483153, 0]], ![![4101652858, 154461, -4], ![9018297951, 380653, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![23191344, 0, 0], ![-10547760, 48, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl
