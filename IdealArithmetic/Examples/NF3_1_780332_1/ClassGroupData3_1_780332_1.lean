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

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-84, -10, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![9, 0, 0], ![-84, -10, 1]] ![![9, 0, 0], ![-84, -10, 1]]
  ![![81, 0, 0], ![-63, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![81, 0, 0], ![-756, -90, 9]], ![![-756, -90, 9], ![-4104, -242, 56]]]
 hmul := by decide
 f := ![![![![86478591, -236461430, -32175183], ![-547972875, -83340819, 0]], ![![0, 0, 0], ![664560, -234, 0]]], ![![![-67261529, 183915878, 25025334], ![426204425, 64821137, 0]], ![![0, 0, 0], ![-516884, 182, 0]]]]
 g := ![![![![540, 74, -1], ![-423, -126, 0]], ![![-4206, -582, 7], ![3426, 996, 0]]], ![![![-4206, -582, 7], ![3426, 996, 0]], ![![-25257, -3466, 47], ![19849, 5900, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![81, 0, 0], ![-63, -4, 1]] ![![9, 0, 0], ![-84, -10, 1]]
  ![![729, 0, 0], ![-1980, -221, 26]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![729, 0, 0], ![-6804, -810, 81]], ![![-567, -36, 9], ![-2520, -212, 17]]]
 hmul := by decide
 f := ![![![![-6071522639432667, 16594937064058099, 2264658033731094], ![38480354345055600, 5851805304121236, 0]], ![![-3098009885753898, 688276089, 0], ![91072080, -1080, 0]]], ![![![13177688324800562, -36017803339735150, -4915234530617220], ![-83518113379612378, -12700811808605720, 0]], ![![6723949020048460, -1493840727, 0], ![-197663680, 2344, 0]]]]
 g := ![![![![5085, -211, -130], ![-9207, -1512, 0]], ![![-28620, 3098, 887], ![79020, 12222, 0]]], ![![![-1167, 432, 61], ![7572, 1092, 0]], ![![-9984, 1322, 329], ![30998, 4732, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![729, 0, 0], ![-1980, -221, 26]] ![![9, 0, 0], ![-84, -10, 1]]
  ![![6561, 0, 0], ![-504, 5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![6561, 0, 0], ![-61236, -7290, 729]], ![![-17820, -1989, 234], ![-102078, -6772, 1270]]]
 hmul := by decide
 f := ![![![![23961739153093568512819419, -65130241549627235920564928, -8924189529201103783544142], ![-152267540321420944406080236, -23121585831234713116550931, 0]], ![![4266169550540769930828804, -5468427524310372, 0], ![7296366276, -23166, 0]]], ![![![-1855622891406772683374024, 5043756063371452304254512, 691098850205964119374041], ![11791762343851149608916721, 1790560513155674025502814, 0]], ![![-330376765477139925762251, 423480918028403, 0], ![-565038464, 1794, 0]]]]
 g := ![![![![9081, -6100, 80], ![1620, -105300, 0]], ![![-81468, 55975, -738], ![9747, 966600, 0]]], ![![![-23724, 16306, -215], ![2949, 281580, 0]], ![![-136982, 94003, -1239], ![14149, 1623240, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![6561, 0, 0], ![-504, 5, 1]] ![![9, 0, 0], ![-84, -10, 1]]
  ![![59049, 0, 0], ![-13545, 167, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![59049, 0, 0], ![-551124, -65610, 6561]], ![![-4536, 45, 9], ![39546, 4558, -514]]]
 hmul := by decide
 f := ![![![![-2502099369764797296710349, 6875633486289604175994708, 920507840800775529236374], ![15815613337571967410329020, 2408626119470722740544257, 0]], ![![-10149648706506059683456428, -1387157624948529540, 0], ![-183376146564, 1438560, 0]]], ![![![574806611849831568551477, -1579537422187546533381192, -211468017435948508993043], ![-3633316576771814992611175, -553333027327415533150247, 0]], ![![2331676053697735517647597, 318671346203678560, 0], ![42126952580, -330480, 0]]]]
 g := ![![![![28638, -400679, 4983], ![52245, -1762236, 0]], ![![-134883, 3683939, -45844], ![79785, 16209396, 0]]], ![![![8043, 30690, -384], ![40647, 135534, 0]], ![![10793, -264479, 3291], ![-889, -1163652, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![59049, 0, 0], ![-13545, 167, 1]] ![![9, 0, 0], ![-84, -10, 1]]
  ![![-225729, -67622, -5230]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![531441, 0, 0], ![-4960116, -590490, 59049]], ![![-121905, 1503, 9], ![1225386, 141448, -15175]]]
 hmul := by decide
 f := ![![![![4620542038967300413388340827, -12698668041480071863199747308, -1697179244979487776476808208], ![-29204003344825778207677773086, -4447766657803309903041922883, 0]], ![![6232763154206070838519819970, 3391281150729396980, 0], ![4879760022724, -1296636, 0]]]]
 g := ![![![![71055, 1822, -566]], ![![-199296, -27962, 3355]]], ![![![-17175, -417, 135]], ![![50746, 7000, -845]]]]
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

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-84, -10, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![9, 0, 0], ![-84, -10, 1]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![27, 0, 0], ![654, 35, -8]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 9, 0]], ![![-252, -30, 3], ![642, 50, -11]]]
 hmul := by decide
 f := ![![![![1632095602, -872439292, 67884955], ![2652155355, -230590449, 0]], ![![78645312, 0, 0], ![-589320, 36, 0]]], ![![![36359852396, -19436216755, 1512342150], ![59084760146, -5137097830, 0]], ![![1752061544, 0, 0], ![-13128880, 802, 0]]]]
 g := ![![![![-105, 655, 132], ![1233, 180, 0]], ![![-429, -408, -71], ![-699, -105, 0]]], ![![![-162, -5625, -1109], ![-10437, -1530, 0]], ![![-230, 14780, 2929], ![27518, 4030, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![654, 35, -8]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![9, 0, 0], ![-84, -10, 1]] ![![9, 0, 0], ![-4, 1, 0]]
  ![![81, 0, 0], ![-1833, -172, 22]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![81, 0, 0], ![-36, 9, 0]], ![![-756, -90, 9], ![894, 80, -14]]]
 hmul := by decide
 f := ![![![![736531760725, -209438543505, 6465694326], ![1652668160121, -58474900422, 0]], ![![0, 0, 0], ![-182346768, 108, 0]]], ![![![-14321676693093, 4072480328901, -125723816235], ![-32135720864125, 1137029878673, 0]], ![![0, 0, 0], ![3545687500, -2100, 0]]]]
 g := ![![![![5058, -21792, -2198], ![-46791, -7020, 0]], ![![-1224, 10067, 992], ![21444, 3210, 0]]], ![![![-36063, 201582, 20107], ![431181, 64620, 0]], ![![46326, -238872, -23902], ![-511496, -76680, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![-1833, -172, 22]] i)) := by 
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

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![729, 0, 0], ![-1980, -221, 26]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![729, 0, 0], ![-1980, -221, 26]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![2187, 0, 0], ![57717, 4720, -703]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![2187, 0, 0], ![-729, 729, 0]], ![![-5940, -663, 78], ![16488, 1465, -247]]]
 hmul := by decide
 f := ![![![![796246017921069271574852, -427881698519539908900996, 32523432676386762588212], ![1293899779121737566309135, -111946962241714200028545, 0]], ![![134366515518915423661113, -718548208497, 0], ![-6202413, 405, 0]]], ![![![17920571652379169234679834, -9630044564720477218078907, 731982945648206606916112], ![29120928935116150006354731, -2519514714003495136561602, 0]], ![![3024096466220488649036503, -16171879502367, 0], ![-139593523, 9115, 0]]]]
 g := ![![![![135567, -506040, 9766], ![2923614, 430920, 0]], ![![-57231, 177902, -3334], ![-1031886, -152145, 0]]], ![![![-416397, 1361206, -25733], ![-7886283, -1162665, 0]], ![![1096423, -3788490, 72268], ![21922421, 3231655, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2187, 0, 0], ![57717, 4720, -703]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![729, 0, 0], ![-1980, -221, 26]] ![![9, 0, 0], ![-4, 1, 0]]
  ![![6561, 0, 0], ![34461, 104, -422]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![6561, 0, 0], ![-2916, 729, 0]], ![![-17820, -1989, 234], ![22428, 2128, -325]]]
 hmul := by decide
 f := ![![![![3172054732005041131724367, -905154069377347671927551, 28043191202001174695940], ![7136887451072751899679843, -252401100806732199012999, 0]], ![![38568425770214790408, -74308208328, 0], ![-112619079, 5589, 0]]], ![![![16641226965119597623558259, -4748617404022180884636175, 147120131601186053360258], ![37441524163974231265939763, -1324146132281864580549063, 0]], ![![202337595393197000352, -389835568624, 0], ![-590821979, 29321, 0]]]]
 g := ![![![![91393506, 191128204, 29801634], ![481324923, 72986508, 0]], ![![-40856346, -85347534, -13307228], ![-214924806, -32591781, 0]]], ![![![-247797279, -518018386, -80770764], ![-1304525853, -197816607, 0]], ![![311954587, 652177288, 101689401], ![1642381909, 249048128, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6561, 0, 0], ![34461, 104, -422]] i)) := by 
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
