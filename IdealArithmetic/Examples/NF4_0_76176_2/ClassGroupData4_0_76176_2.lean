import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF4_0_76176_2.RI4_0_76176_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section 


def alpha0 := B.equivFun.symm ![-2, 0, 1, -2]

def alpha1 := B.equivFun.symm ![0, 0, -1, 2]

def v := B.equivFun.symm ![-1, 0, 0, 0]

def zeta1 := B.equivFun.symm ![3, -1, -1, 2]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, -1, 0, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0], ![0, -1, 0, 0]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![2, 0, 0, 0], ![0, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0], ![0, -2, 0, 0]], ![![0, -2, 0, 0], ![0, 0, 1, 0]]]
 hmul := by decide
 f :=  ![![![![-33013, 49602, 26208, -72345], ![37203, -13104, -4095, 0]], ![![0, 0, 0, 0], ![1269, 72, 3, 0]]], ![![![-24, 36, 20, -53], ![27, -8, -3, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]]]]
 g :=  ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![4, 0, 0, -1], ![0, -2, 0, 0]]], ![![![4, 0, 0, -1], ![0, -2, 0, 0]], ![![0, 0, 0, 1], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0], ![0, 0, 1, -2]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![4, 0, 0, 0], ![0, 1, 0, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M :=  ![![![4, 0, 0, 0], ![0, -2, 0, 0]], ![![0, 0, 2, -4], ![-4, -1, 0, 1]]]
 hmul := by decide
 f :=  ![![![![514, -648, -356, 954], ![-486, 179, 54, 0]], ![![0, 0, 0, 0], ![72, -6, 0, 0]]], ![![![-1, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![-1, 0, 0, 0]]]]
 g :=  ![![![![13699, -14904, -20454, 37635], ![-13134, 9096, -6, 0]], ![![-20169, 21942, 30114, -55409], ![19339, -13392, 9, 0]]], ![![![13437, -14619, -20062, 36914], ![-12882, 8922, -6, 0]], ![![-27145, 29532, 40530, -74574], ![26027, -18024, 12, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0], ![0, 1, 0, -1]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![4, 0, 0, 0], ![-2, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0], ![0, -4, 0, 0]], ![![0, 2, 0, -2], ![6, -8, -9, 18]]]
 hmul := by decide
 f :=  ![![![![-5489649, 8190336, 4403284, -11992992], ![6142752, -2201642, -682528, 0]], ![![156148, -18725, 0, 0], ![1605, -36, 3, 0]]], ![![![5499896, -8205624, -4411503, 12015378], ![-6154218, 2205752, 683802, 0]], ![![-156440, 18760, 0, 0], ![-1608, 36, -3, 0]]]]
 g :=  ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![-4, 0, 0, 1], ![0, 4, 0, 0]]], ![![![2, 0, 0, -1], ![0, -2, 0, 0]], ![![-5, 0, -3, 8], ![3, 8, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0], ![-2, 0, 1, -2]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![8, 0, 0, 0], ![2, -4, -5, 10]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M :=  ![![![8, 0, 0, 0], ![0, -4, 0, 0]], ![![-4, 0, 2, -4], ![-4, 1, 0, 1]]]
 hmul := by decide
 f :=  ![![![![11984, -17976, -9620, 26322], ![-13482, 4811, 1498, 0]], ![![124, 0, 0, 0], ![-144, -12, 0, 0]]], ![![![3416, -5124, -2742, 7503], ![-3843, 1372, 427, 0]], ![![35, 0, 0, 0], ![-40, -3, 0, 0]]]]
 g :=  ![![![![22117, 2436, 3204, -3135], ![-1590, 8616, 42, 0]], ![![-18300, -2011, -2644, 2580], ![1325, -7128, -35, 0]]], ![![![-7394, -812, -1068, 1042], ![536, -2880, -14, 0]], ![![-7403, -810, -1066, 1037], ![542, -2883, -14, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![8, 0, 0, 0], ![2, -4, -5, 10]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![-2, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M :=  ![![![16, 0, 0, 0], ![0, -8, 0, 0]], ![![4, -8, -10, 20], ![20, 3, 4, -5]]]
 hmul := by decide
 f :=  ![![![![-14459280, 21727692, 11592176, -31689922], ![16295771, -5796088, -1807410, 0]], ![![44893, 4998, 0, 0], ![357, 381, -7, 0]]]]
 g :=  ![![![![-2, 0, -2, 4]], ![![4, 2, 0, -1]]], ![![![-4, 2, 2, -5]], ![![-1, -3, -5, 10]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 =  Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![6, -1, 0, 2]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![6, 0, 0, 0], ![6, -1, 0, 2]] ![![6, 0, 0, 0], ![6, -1, 0, 2]]
  ![![0, 0, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![36, 0, 0, 0], ![36, -6, 0, 12]], ![![36, -6, 0, 12], ![-28, -28, -23, 56]]]
 hmul := by decide
 f :=  ![![![![86187430474438177, 502863385707409944, 1015647619543521774, -1932396709785171635], ![-641755370405187355, 338549206514507258, 13021120546113365, 0]], ![![0, 0, 0, 0], ![18856689989, 1754528, -6, 0]]]]
 g :=  ![![![![-6, 0, 6, -12]], ![![-10, 12, 14, -29]]], ![![![-10, 12, 14, -29]], ![![9, 10, 2, -1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 =  Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1, 1, 1, -2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![6, -1, 0, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, -1, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulRJ0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0, 0], ![0, -1, 0, 0]] ![![6, 0, 0, 0], ![6, -1, 0, 2]]
  ![![6, 0, 0, 0], ![2, -2, -3, 6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M :=  ![![![12, 0, 0, 0], ![12, -2, 0, 4]], ![![0, -6, 0, 0], ![-12, 10, 17, -36]]]
 hmul := by decide
 f :=  ![![![![-9999103555, -58339837585, -117830619243, 224187510950], ![74453373030, -39276873081, -1510656345, 0]], ![![0, 0, 0, 0], ![-21321, -810, -9, 0]]], ![![![-3306887897, -19294059881, -38968758186, 74142943139], ![24623103131, -12989586062, -499601905, 0]], ![![0, 0, 0, 0], ![-7052, -268, -3, 0]]]]
 g :=  ![![![![326, 34, 48, -68], ![6, 156, 6, 0]], ![![146, 14, 22, -31], ![2, 70, 2, 0]]], ![![![-540, -60, -78, 109], ![-12, -258, -12, 0]], ![![-209, -18, -27, 36], ![0, -100, -3, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![2, -2, -3, 6]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulRJ0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, 0, 1, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00] 
 rfl     
def MulRJ0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![2, 0, 0, 0], ![0, 0, 1, -2]] ![![6, 0, 0, 0], ![6, -1, 0, 2]]
  ![![12, 0, 0, 0], ![0, -5, -2, 5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M :=  ![![![12, 0, 0, 0], ![12, -2, 0, 4]], ![![0, 0, 6, -12], ![-4, 11, 14, -27]]]
 hmul := by decide
 f :=  ![![![![47677336, 278175034, 561838113, -1068967304], ![-355007604, 187279371, 7203042, 0]], ![![0, 0, 0, 0], ![-36, -18, 0, 0]]], ![![![941131, 5491036, 11090400, -21100878], ![-7007660, 3696800, 142186, 0]], ![![0, 0, 0, 0], ![5, 0, 0, 0]]]]
 g :=  ![![![![-691538837, -1922920031, -3884303277, 5384444230], ![3692118990, -4153261404, 91554, 0]], ![![-385047267, -1070677539, -2162771315, 2998046417], ![2055763547, -2312526596, 50977, 0]]], ![![![231177309, 642820699, 1298499421, -1799987596], ![-1234253358, 1388410518, -30606, 0]], ![![-916732465, -2549102269, -5149192969, 7137841819], ![4894425541, -5505734980, 121368, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0, 0], ![0, -5, -2, 5]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulRJ0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0], ![0, 1, 0, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01] 
 rfl     
def MulRJ0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![4, 0, 0, 0], ![0, 1, 0, -1]] ![![6, 0, 0, 0], ![6, -1, 0, 2]]
  ![![12, 0, 0, 0], ![0, 1, 6, -11]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M :=  ![![![24, 0, 0, 0], ![24, -4, 0, 8]], ![![0, 6, 0, -6], ![38, 6, 3, -4]]]
 hmul := by decide
 f :=  ![![![![7286670267674, 42514289872058, 85867399078272, -163373443240054], ![-54256859124342, 28622466359424, 1100865097125, 0]], ![![139366305, 1939665, 0, 0], ![-28665, -810, 9, 0]]], ![![![-4845578548074, -28271669146917, -57101146568661, 108642057731056], ![36080385553436, -19033715522887, -732066650883, 0]], ![![-92677485, -1289862, 0, 0], ![19062, 539, -6, 0]]]]
 g :=  ![![![![-197298, 9284, 23034, -36744], ![45996, 78936, 12, 0]], ![![-197958, 9315, 23112, -36868], ![46148, 79200, 12, 0]]], ![![![990, -47, -120, 192], ![-222, -396, 0, 0]], ![![-311481, 14658, 36369, -58017], ![72607, 124619, 19, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0, 0], ![0, 1, 6, -11]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulRJ0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0], ![-2, 0, 1, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02] 
 rfl     
def MulRJ0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![4, 0, 0, 0], ![-2, 0, 1, -2]] ![![6, 0, 0, 0], ![6, -1, 0, 2]]
  ![![24, 0, 0, 0], ![-10, 4, 9, -18]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M :=  ![![![24, 0, 0, 0], ![24, -4, 0, 8]], ![![-12, 0, 6, -12], ![-16, 13, 14, -31]]]
 hmul := by decide
 f :=  ![![![![-951658830116, -5552482003735, -11214507025107, 21337003266110], ![7086089259210, -3738169008369, -143775772650, 0]], ![![-718284, 16632, 0, 0], ![-792, -36, 0, 0]]], ![![![391701854744, 2285396226556, 4615880253303, -8782289923241], ![-2916627490755, 1538626751101, 59177969071, 0]], ![![295645, -6846, 0, 0], ![326, 15, 0, 0]]]]
 g :=  ![![![![-1302619293, 17618268, -202518707, 442365003], ![137976186, 907130856, -1408590, 0]], ![![-1178107289, 15934211, -183160779, 400081157], ![124787611, 820421960, -1273949, 0]]], ![![![744262844, -10066352, 115710817, -252749076], ![-78833880, -518297088, 804810, 0]], ![![680761945, -9207490, 105838300, -231184373], ![-72107710, -474075701, 736144, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0, 0], ![-10, 4, 9, -18]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulRJ0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0, 0], ![2, -4, -5, 10]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03] 
 rfl     
def MulRJ0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![8, 0, 0, 0], ![2, -4, -5, 10]] ![![6, 0, 0, 0], ![6, -1, 0, 2]]
  ![![24, 0, 0, 0], ![0, -1, 6, -13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M :=  ![![![48, 0, 0, 0], ![48, -8, 0, 16]], ![![12, -24, -30, 60], ![-16, -17, -2, -5]]]
 hmul := by decide
 f :=  ![![![![-31512215129896294, -183858980023844292, -371345261043436839, 706530837296920314], ![234641227306384530, -123781753681145613, -4760838449218062, 0]], ![![12244504410, 27156465, 0, 0], ![431055, -7524, -63, 0]]], ![![![7034368610043265, 41042238142354245, 82894186809928371, -157716565573770203], ![-52378192938272509, 27631395603309457, 1062746379669591, 0]], ![![-2733300630, -6062049, 0, 0], ![-96223, 1680, 14, 0]]]]
 g :=  ![![![![-2911266, -2335311, -710640, 2968393], ![-1688208, 3881904, 120, 0]], ![![-2911374, -2335398, -710666, 2968503], ![-1688272, 3882048, 120, 0]]], ![![![-728118, -584070, -177738, 742415], ![-422214, 970878, 30, 0]], ![![970194, 778254, 236821, -989225], ![562617, -1293664, -40, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0, 0], ![0, -1, 6, -13]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulRJ0_5J1_1]
 rfl
