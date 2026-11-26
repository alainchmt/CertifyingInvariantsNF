import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_780332_1.RI3_1_780332_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-225729, -67622, -5230]

def alpha1 := B.equivFun.symm ![13, -1, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![44015, 7818, -868]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 0, 0], ![165, 14, -2]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![9, 0, 0], ![165, 14, -2]] ![![9, 0, 0], ![165, 14, -2]]
  ![![81, 0, 0], ![-63, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![81, 0, 0], ![1485, 126, -18]], ![![1485, 126, -18], ![-4023, -92, 32]]]
 hmul := by decide
 f := ![![![![-178621995, 474847690, 21962112], ![-2540963340, -377100360, 0]], ![![0, 0, 0], ![-51480, -234, 0]]], ![![![138871336, -369175264, -17074669], ![1975498245, 293180576, 0]], ![![0, 0, 0], ![40024, 182, 0]]]]
 g := ![![![![540, 74, -1], ![-423, -126, 0]], ![![8850, 1212, -17], ![-6873, -2058, 0]]], ![![![8850, 1212, -17], ![-6873, -2058, 0]], ![![-25995, -3566, 48], ![20440, 6074, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![81, 0, 0], ![-63, -4, 1]] ![![9, 0, 0], ![165, 14, -2]]
  ![![729, 0, 0], ![12834, 725, -152]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![729, 0, 0], ![13365, 1134, -162]], ![![-567, -36, 9], ![1881, 70, -13]]]
 hmul := by decide
 f := ![![![![-196370084874071526, 521924436845288687, 24159132700973492], ![-2793604461532187157, -414614002219275474, 0]], ![![-405776392558866, 86253525, 0], ![-5571396, 1728, 0]]], ![![![-3237391619059413596, 8604537695794139372, 398291693869929884], ![-46055852532380571592, -6835399072064035704, 0]], ![![-6689700691042936, 1421990725, 0], ![-91851016, 28488, 0]]]]
 g := ![![![![3411, 32345, 7310], ![126495, 19170, 0]], ![![92853, 588366, 132208], ![2292372, 347670, 0]]], ![![![-15363, -25674, -5489], ![-96870, -14790, 0]], ![![6025, 82910, 18805], ![325004, 49230, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![729, 0, 0], ![12834, 725, -152]] ![![9, 0, 0], ![165, 14, -2]]
  ![![6561, 0, 0], ![-504, 5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![6561, 0, 0], ![120285, 10206, -1458]], ![![115506, 6525, -1368], ![121086, 25261, -2902]]]
 hmul := by decide
 f := ![![![![1654918549896307328196147, -4398525299521339499076300, -203593431895343882622302], ![23543265933709182658951650, 3494202980612920083780516, 0]], ![![-16533535412111563395, 219663197082, 0], ![-29148417, 162, 0]]], ![![![-132801963917372948540433, 352967702339964183273128, 16337727073077818642485], ![-1889272407528132620069893, -280398704927447524408964, 0]], ![![1326763769348904455, -17627274753, 0], ![2339068, -13, 0]]]]
 g := ![![![![9081, -6100, 80], ![1620, -105300, 0]], ![![161613, -110489, 1455], ![-8613, -1907820, 0]]], ![![![155682, -106520, 1403], ![-9951, -1839300, 0]], ![![159902, -109294, 1439], ![-8081, -1887220, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![6561, 0, 0], ![-504, 5, 1]] ![![9, 0, 0], ![165, 14, -2]]
  ![![59049, 0, 0], ![-13545, 167, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![59049, 0, 0], ![1082565, 91854, -13122]], ![![-4536, 45, 9], ![-80928, -6851, 995]]]
 hmul := by decide
 f := ![![![![-2236502091404168226988790391021, 5944284264109824048853986656668, 275141614116568677322839075516], ![-31817016512487039791537808827634, -4722164774888282251132010564988, 0]], ![![-512914751951827375459492740, -70100319022861882500, 0], ![4509194060880, -913680, 0]]], ![![![514232947239045195099105694626, -1366753390532589244670578729392, -63262575822784003911291265098], ![7315601553181308419309657771769, 1085754723356695585663515293352, 0]], ![![117933117787953448038035877, 16117978960123044960, 0], ![-1036786936400, 210080, 0]]]]
 g := ![![![![28638, -400679, 4983], ![52245, -1762236, 0]], ![![289998, -7267145, 90429], ![-53055, -31974264, 0]]], ![![![8043, 30690, -384], ![40647, 135534, 0]], ![![-11538, 543149, -6761], ![48178, 2390318, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![59049, 0, 0], ![-13545, 167, 1]] ![![9, 0, 0], ![165, 14, -2]]
  ![![-225729, -67622, -5230]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![531441, 0, 0], ![9743085, 826686, -118098]], ![![-121905, 1503, 9], ![-2413485, -202871, 29345]]]
 hmul := by decide
 f := ![![![![580826214518767862802462951800737135, -1543747636847021995251243550876114736, -71455192947458065786154526975529256], ![8262974318403700617829031820978565186, 1226360383755842244115990326730928620, 0]], ![![4938676893978799343736329685730, 2687165244037875144748, 0], ![-1955602637014480, 13435840, 0]]]]
 g := ![![![![71055, 1822, -566]], ![![585459, 54736, -7736]]], ![![![-17175, -417, 135]], ![![-145987, -13571, 1923]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![9, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![1, -2, 1]]]
 hmul := by decide
 f := ![![![![0, 2157, -794], ![0, -981, 0]], ![![0, 0, 0], ![10053, -18, 0]]], ![![![0, -1197, 440], ![0, 548, 0]], ![![0, 0, 0], ![-5584, 10, 0]]]]
 g := ![![![![37, -9, 0], ![81, 0, 0]], ![![-7, 6, -1], ![-15, 9, 0]]], ![![![-7, 6, -1], ![-15, 9, 0]], ![![5, -1, 0], ![11, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![9, 0, 0], ![-4, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![13, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 9, 0]], ![![-12, 3, 0], ![4, -5, 1]]]
 hmul := by decide
 f := ![![![![375288, -718050, 82562], ![609843, 141776, 0]], ![![375288, -1158008, 0], ![-31274, -28, 0]]]]
 g := ![![![![45, 13, 1]], ![![171, 52, 4]]], ![![![42, 13, 1]], ![![172, 51, 4]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-254704705, -76301322, -5901568])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![165, 14, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![9, 0, 0], ![165, 14, -2]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![27, 0, 0], ![-402, -32, 5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 9, 0]], ![![495, 42, -6], ![-1281, -97, 16]]]
 hmul := by decide
 f := ![![![![299496948, -164354269, 12013409], ![486682542, -41043090, 0]], ![![-6932565, 0, 0], ![214344, -9, 0]]], ![![![-3394656758, 1862878175, -136166330], ![-5516317230, 465204085, 0]], ![![78577358, 0, 0], ![-2429488, 102, 0]]]]
 g := ![![![![147, -32, 27], ![-1989, -288, 0]], ![![15, 27, -17], ![1167, 168, 0]]], ![![![2547, -546, 463], ![-34143, -4944, 0]], ![![-6071, 1469, -1214], ![89042, 12888, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-402, -32, 5]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![9, 0, 0], ![165, 14, -2]] ![![9, 0, 0], ![-4, 1, 0]]
  ![![81, 0, 0], ![-3180, -266, 38]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![81, 0, 0], ![-36, 9, 0]], ![![1485, 126, -18], ![-1776, -139, 22]]]
 hmul := by decide
 f := ![![![![7903516004273, -2247412139953, 69386917140], ![17734357351989, -626888066085, 0]], ![![0, 0, 0], ![984195576, -27, 0]]], ![![![-232440951967172, 66095977662566, -2040656470563], ![-521564187786004, 18436662718335, 0]], ![![0, 0, 0], ![-28945010864, 794, 0]]]]
 g := ![![![![1929, -9586, -532], ![-21735, -3267, 0]], ![![1140, 4723, 228], ![10371, 1551, 0]]], ![![![25521, -172430, -9420], ![-389484, -58509, 0]], ![![-28348, 206785, 11260], ![466720, 70103, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![-3180, -266, 38]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![-63, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![81, 0, 0], ![-63, -4, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![243, 0, 0], ![-144, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![243, 0, 0], ![-81, 81, 0]], ![![-189, -12, 3], ![621, 65, -5]]]
 hmul := by decide
 f := ![![![![188667766710, -105189788311, 7112469233], ![306585120906, -25455169722, 0]], ![![111179847969, 71847, 0], ![702, 702, 0]]], ![![![-111809813014, 62338420426, -4215048861], ![-181690946146, 15085447912, 0]], ![![-65888297876, -42580, 0], ![-412, -416, 0]]]]
 g := ![![![![3591, -204, -26], ![-1998, -2079, 0]], ![![-2619, 159, 19], ![1719, 1584, 0]]], ![![![-2481, 148, 18], ![1569, 1485, 0]], ![![7867, -453, -57], ![-4546, -4598, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![243, 0, 0], ![-144, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![81, 0, 0], ![-63, -4, 1]] ![![9, 0, 0], ![-4, 1, 0]]
  ![![729, 0, 0], ![-144, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![729, 0, 0], ![-324, 81, 0]], ![![-567, -36, 9], ![810, 77, -8]]]
 hmul := by decide
 f := ![![![![-14614449371755, 4167276726159, -128687137105], ![-32872749023331, 1158804542025, 0]], ![![-5590166400, 0, 0], ![-8255520, 6480, 0]]], ![![![2886854382024, -823179907224, 25420117871], ![6493494017680, -228903592934, 0]], ![![1104249360, 0, 0], ![1630748, -1280, 0]]]]
 g := ![![![![236727, -9064, -1699], ![-46089, -321165, 0]], ![![-108954, 4181, 782], ![21942, 148005, 0]]], ![![![-182241, 6988, 1308], ![36297, 247455, 0]], ![![259296, -9931, -1861], ![-50719, -351845, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![729, 0, 0], ![-144, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![729, 0, 0], ![12834, 725, -152]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![729, 0, 0], ![12834, 725, -152]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![2187, 0, 0], ![-36000, -3182, 422]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![2187, 0, 0], ![-729, 729, 0]], ![![38502, 2175, -456], ![-97650, -6739, 877]]]
 hmul := by decide
 f := ![![![![912770094324884939813174, -511415112650612575567431, 35676195930225720760394], ![1483251403277938027196409, -121892928581348881161780, 0]], ![![-23763386919854850235641, 434874501486, 0], ![22021713, -405, 0]]], ![![![-12634567485315734965744250, 7079010140635314967049144, -493830054142139209166492], ![-20531172163638069319334406, 1687242430179426929842874, 0]], ![![328932901708006636212058, -6019534678918, 0], ![-304824644, 5606, 0]]]]
 g := ![![![![432801, -1390448, -139392], ![-4530168, -696600, 0]], ![![-118827, 485667, 48040], ![1575180, 241920, 0]]], ![![![6990546, -24474859, -2441024], ![-79601844, -12234600, 0]], ![![-17651990, 62047345, 6186949], ![201786817, 31013480, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2187, 0, 0], ![-36000, -3182, 422]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![729, 0, 0], ![12834, 725, -152]] ![![9, 0, 0], ![-4, 1, 0]]
  ![![6561, 0, 0], ![-189639, -11761, 2308]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![6561, 0, 0], ![-2916, 729, 0]], ![![115506, 6525, -1368], ![-136152, -8914, 1333]]]
 hmul := by decide
 f := ![![![![24841076659786288621920351833, -7085092908169339207417010479, 218758870977797470592943081], ![55890583864766087052403801863, -1968916941870899930417775888, 0]], ![![-46416767928633611619786, 4670104871538, 0], ![1124647497, -13608, 0]]], ![![![-689380056332996525591081914641, 196622787935163264746111242547, -6070912499624086828463231458], ![-1551054102077232173758048161703, 54640629747713582552293206968, 0]], ![![1288140386492907988493375, -129602963813307, 0], ![-31210787095, 377644, 0]]]]
 g := ![![![![158247, 3652770, 852544], ![-9724374, -1432728, 0]], ![![57429, -1642716, -386840], ![4398975, 647460, 0]]], ![![![2235204, 64029303, 14958612], ![-170566146, -25127388, 0]], ![![-2468393, -75418241, -17623703], ![200937785, 29600824, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6561, 0, 0], ![-189639, -11761, 2308]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6561, 0, 0], ![-504, 5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![6561, 0, 0], ![-504, 5, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![19683, 0, 0], ![-504, 5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![19683, 0, 0], ![-6561, 6561, 0]], ![![-1512, 15, 3], ![1062, -385, 4]]]
 hmul := by decide
 f := ![![![![-10740516252039971534, 6310586970499727215, -434202341751027976], ![-17453338909564953741, 1331908979929738782, 0]], ![![-64083462590588386176, 17542527456402, 0], ![81420066, 12636, 0]]], ![![![287306334469299628, -168806747115124744, 11614812575026838], ![466872793512611896, -35628258259716015, 0]], ![![1714217855543534198, -469258566586, 0], ![-2177968, -338, 0]]]]
 g := ![![![![209961, -142900, 1880], ![4860, -7401780, 0]], ![![-70083, 47912, -631], ![10773, 2481840, 0]]], ![![![-15840, 10975, -145], ![10938, 568620, 0]], ![![11682, -7730, 101], ![13121, -400220, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![19683, 0, 0], ![-504, 5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![6561, 0, 0], ![-504, 5, 1]] ![![9, 0, 0], ![-4, 1, 0]]
  ![![59049, 0, 0], ![-504, 5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![59049, 0, 0], ![-26244, 6561, 0]], ![![-4536, 45, 9], ![2574, -400, 1]]]
 hmul := by decide
 f := ![![![![-19392109120424219332965, 5527960074564028794075, -169987291976062430498], ![-43632086824345347039519, 1529886887279356038021, 0]], ![![-918172960357211244, 251071497234, 0], ![535452687, 112266, 0]]], ![![![172913294580766674614, -49291069004818832109, 1515722839115329779], ![389053497759328372958, -13641516782554102884, 0]], ![![8187057456433494, -2238725014, 0], ![-4774462, -1001, 0]]]]
 g := ![![![![209961, -142900, 1880], ![14580, -22205340, 0]], ![![-93348, 63604, -837], ![5913, 9883620, 0]]], ![![![-15840, 10975, -145], ![32814, 1705860, 0]], ![![9174, -6235, 82], ![2183, -968840, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![59049, 0, 0], ![-504, 5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![59049, 0, 0], ![-13545, 167, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![59049, 0, 0], ![-13545, 167, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![177147, 0, 0], ![-13545, 167, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![177147, 0, 0], ![-59049, 59049, 0]], ![![-40635, 501, 3], ![14103, -13588, 166]]]
 hmul := by decide
 f := ![![![![-4447565274138672315182653602, 2617274777002539179934321134, -182893603373591844381800818], ![-7227293570475342512171812101, 549132297920847096955510551, 0]], ![![-8886634368766957107703477980, -249298559623593, 0], ![-9169016454, -34263, 0]]], ![![![340872220019389266044227230, -200594304669398009204435394, 14017410598066039158803189], ![553917357531507557321869251, -42086834917308405893662881, 0]], ![![681093272176616034315542436, 19106847955815, 0], ![702735722, 2626, 0]]]]
 g := ![![![![587581164, -14239650781, 177187637], ![-58301775, -187953293592, 0]], ![![-195991137, 4749787491, -59102828], ![19484226, 62693827470, 0]]], ![![![-134774706, 3266400532, -40644664], ![13493793, 43114172454, 0]], ![![46818199, -1134389962, 14115504], ![-4526362, -14973141680, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![177147, 0, 0], ![-13545, 167, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![59049, 0, 0], ![-13545, 167, 1]] ![![9, 0, 0], ![-4, 1, 0]]
  ![![531441, 0, 0], ![163602, 167, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![531441, 0, 0], ![-236196, 59049, 0]], ![![-121905, 1503, 9], ![54738, -14089, 163]]]
 hmul := by decide
 f := ![![![![12023795327315106435137910328822100569, -3427470401549097674972412872724001743, 105380680733251481342531483499010275], ![27053528555552187831957819198494283465, -948426129827290414894935461076675018, 0]], ![![21179085869459433770910035461422, -1072628157051539276247, 0], ![-85719998315259, -110157003, 0]]], ![![![3701314906775830082519478079000807380, -1055086762909778423498820270025956126, 32439597803039540540567833033376962], ![8327955175357311777679036040175074442, -291956381221047493493046546702707223, 0]], ![![6519610830569585675139764065614, -330189801060833010459, 0], ![-26387400894316, -33909905, 0]]]]
 g := ![![![![62489943, 20682162005, 21095699], ![25979373, -67132606896, 0]], ![![-27844668, -9192465555, -9376268], ![-11318940, 29837991384, 0]]], ![![![-14456115, -4744203680, -4839064], ![-5563719, 15399296856, 0]], ![![6442028, 2130340114, 2172936], ![2658659, -6914909816, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![531441, 0, 0], ![163602, 167, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl
