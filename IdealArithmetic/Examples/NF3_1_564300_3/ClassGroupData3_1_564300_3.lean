import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_564300_3.RI3_1_564300_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-343, -29, -12]

def alpha1 := B.equivFun.symm ![6, 0, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-1, 1, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![1, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![49, 0, 0], ![8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![7, 7, 0]], ![![7, 7, 0], ![1, 2, 5]]]
 hmul := by decide
 f := ![![![![0, -4726, -5565], ![0, -4648, 0]], ![![0, 0, 0], ![88249, -588, 0]]], ![![![0, -724, -855], ![0, -707, 0]], ![![0, 0, 0], ![13508, -90, 0]]]]
 g := ![![![![233, 29, 0], ![-1421, 0, 0]], ![![31, 4, 0], ![-189, 0, 0]]], ![![![31, 4, 0], ![-189, 0, 0]], ![![-7, -1, 0], ![43, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![8, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![343, 0, 0], ![155, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![49, 49, 0]], ![![56, 7, 0], ![8, 9, 5]]]
 hmul := by decide
 f := ![![![![65286956, 38683600, 2993925], ![-219177637, -1661961, 0]], ![![-207561648, -17171952, 0], ![-3706458, -4116, 0]]], ![![![29407734, 17424569, 1348575], ![-98725963, -748605, 0]], ![![-93493680, -7734912, 0], ![-1669530, -1854, 0]]]]
 g := ![![![![17516, 113, 0], ![-38759, 0, 0]], ![![2458, 16, 0], ![-5439, 0, 0]]], ![![![2632, 17, 0], ![-5824, 0, 0]], ![![376, 2, 0], ![-832, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![343, 0, 0], ![155, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![2401, 0, 0], ![-531, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![2401, 0, 0], ![343, 343, 0]], ![![1085, 7, 0], ![155, 156, 5]]]
 hmul := by decide
 f := ![![![![2999638880, -62999724558, 3060701035], ![-10070216233, -7242265457, 0]], ![![-3450712398, 144911264946, 0], ![-25945206, -28812, 0]]], ![![![-664018008, 13945995879, -677535095], ![2229203319, 1603191211, 0]], ![![763870338, -32078424444, 0], ![5743386, 6378, 0]]]]
 g := ![![![![77527, -146, 0], ![350546, 0, 0]], ![![11227, -21, 0], ![50764, 0, 0]]], ![![![35579, -67, 0], ![160874, 0, 0]], ![![5993, -11, 0], ![27098, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![2401, 0, 0], ![-531, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![16807, 0, 0], ![-531, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![16807, 0, 0], ![2401, 2401, 0]], ![![-3717, 7, 0], ![-531, -530, 5]]]
 hmul := by decide
 f := ![![![![2245624392444, -273526290923323, 20367520965670], ![-7538881888916, -24847758641055, 0]], ![![5284190918804, -1257702373427430, 0], ![30269407, -201684, 0]]], ![![![-71014978352, 8649916564070, -644096610880], ![238407427328, 785778355434, 0]], ![![-167105730132, 39773217250367, 0], ![-957231, 6378, 0]]]]
 g := ![![![![2721907, -5126, 0], ![86152682, 0, 0]], ![![389299, -733, 0], ![12321932, 0, 0]]], ![![![-601623, 1664, -5], ![-19042324, 16807, 0]], ![![-85491, 692, -5], ![-2705926, 16808, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![16807, 0, 0], ![-531, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![117649, 0, 0], ![-34145, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![117649, 0, 0], ![16807, 16807, 0]], ![![-3717, 7, 0], ![-531, -530, 5]]]
 hmul := by decide
 f := ![![![![-101671970526, 119893407883174, -8865248867355], ![341327329630, 10809833645282, 0]], ![![-1674745750496, 3845236823243088, 0], ![211885849, -1411788, 0]]], ![![![29508455160, -34796898618689, 2572978544135], ![-99064099460, -3137359193310, 0]], ![![486064739680, -1116010615309304, 0], ![-61496045, 409746, 0]]]]
 g := ![![![![3806348021, -111476, 0], ![13115039924, 0, 0]], ![![543764003, -15925, 0], ![1873577132, 0, 0]]], ![![![-120224543, 37666, -5], ![-414242122, 117649, 0]], ![![-17165179, 34648, -5], ![-59143832, 117650, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![117649, 0, 0], ![-34145, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![823543, 0, 0], ![83504, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![823543, 0, 0], ![117649, 117649, 0]], ![![-239015, 7, 0], ![-34145, -34144, 5]]]
 hmul := by decide
 f := ![![![![454910700421076334, -2779442111326689692909, 188104044649468928170], ![-1527200208556470546, -262768114111395161199, 0]], ![![815701715665413822, -9706855922903927758194, 0], ![1483200943, -9882516, 0]]], ![![![46125868107561192, -281822740421333628067, 19072891330032566910], ![-154851128646812568, -26643487091325479243, 0]], ![![82708429845830616, -984230873497872400653, 0], ![150389804, -1002042, 0]]]]
 g := ![![![![19398229713, 232303, 0], ![-191311509529, 0, 0]], ![![2771151815, 33186, 0], ![-27329980349, 0, 0]]], ![![![-5630006689, -150926, -5], ![55524916153, 823543, 0]], ![![-804382103, -93137, -5], ![7933072071, 823544, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![823543, 0, 0], ![83504, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![5764801, 0, 0], ![-740039, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![5764801, 0, 0], ![823543, 823543, 0]], ![![584528, 7, 0], ![83504, 83505, 5]]]
 hmul := by decide
 f := ![![![![286073229574119776, -1747842747636046591520, 118046570470285914095], ![-960388699284544957, -165413709787741591540, 0]], ![![-1468251050780848425, 17472185855736975429171, 0], ![10342052994, 11529602, 0]]], ![![![-36723815836106076, 224374211002603616878, -15153883921569445830], ![123287096021213257, 21234502172941784835, 0]], ![![188482443010539825, -2242940860196972670954, 0], ![-1327630866, -1480079, 0]]]]
 g := ![![![![2523390162474, -3409807, 0], ![19656858803407, 0, 0]], ![![360484943244, -487116, 0], ![2808127627459, 0, 0]]], ![![![255861823900, -345741, 0], ![1993128062548, 0, 0]], ![![36552112008, -49392, 0], ![284735874536, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![5764801, 0, 0], ![-740039, 1, 0]] ![![7, 0, 0], ![1, 1, 0]]
  ![![-343, -29, -12]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![40353607, 0, 0], ![5764801, 5764801, 0]], ![![-5180273, 7, 0], ![-740039, -740038, 5]]]
 hmul := by decide
 f := ![![![![85132118819148042, -10805664948272482393548, 730167244859924083094], ![-285800684607139854, -1022130550870240160865, 0]], ![![345117717441091920, -85312411816849612798530, 0], ![-591643, 3942, 0]]]]
 g := ![![![![-115999, 9083, -4409]], ![![-35467, 3622, 5858]]], ![![![14891, -1166, 566]], ![![4553, -465, -752]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow9 : J0 ^ 9 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 0, 0], ![0, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![6, 0, 0], ![0, 1, 0]] ![![6, 0, 0], ![0, 1, 0]]
  ![![6, 0, 0], ![18, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![36, 0, 0], ![0, 6, 0]], ![![0, 6, 0], ![0, 0, 5]]]
 hmul := by decide
 f := ![![![![146, -142, 0], ![-23, 0, 0]], ![![0, 0, 0], ![0, -35, 0]]], ![![![438, -426, 116], ![-69, -140, 0]], ![![0, 0, 0], ![5, -105, 0]]]]
 g := ![![![![6, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-5, -4, 0], ![5, -2, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![6, 0, 0], ![18, 0, 1]] ![![6, 0, 0], ![0, 1, 0]]
  ![![6, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![36, 0, 0], ![0, 6, 0]], ![![108, 0, 6], ![30, -12, 0]]]
 hmul := by decide
 f := ![![![![-29, 11, 0], ![4, 0, 0]], ![![0, 0, 0], ![35, 0, 0]]]]
 g := ![![![![6, 0, 0]], ![![0, 1, 0]]], ![![![18, 0, 1]], ![![5, -2, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-151, -1, -5])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![18, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![7, 0, 0], ![1, 1, 0]] ![![6, 0, 0], ![0, 1, 0]]
  ![![42, 0, 0], ![-6, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![42, 0, 0], ![0, 7, 0]], ![![6, 6, 0], ![0, 1, 5]]]
 hmul := by decide
 f := ![![![![0, 68, 105], ![-198, 90, 0]], ![![7, -252, 0], ![0, 0, 0]]], ![![![0, -12, -20], ![37, -12, 0]], ![![-1, 42, 0], ![0, 0, 0]]]]
 g := ![![![![-23, -7340, 6120], ![-168, -51408, 0]], ![![7, 1223, -1020], ![49, 8568, 0]]], ![![![1, 0, 0], ![6, 0, 0]], ![![1, 204, -170], ![7, 1429, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![42, 0, 0], ![-6, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![7, 0, 0], ![1, 1, 0]] ![![6, 0, 0], ![18, 0, 1]]
  ![![42, 0, 0], ![18, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![42, 0, 0], ![126, 0, 7]], ![![6, 6, 0], ![48, -12, 1]]]
 hmul := by decide
 f := ![![![![-18, 0, 4], ![6, 0, 0]], ![![7, -7, 0], ![0, 0, 0]]], ![![![-3, 0, 2], ![1, 0, 0]], ![![3, -3, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![7, 0, 0]]], ![![![28, -11, 0], ![0, -39, 0]], ![![0, 0, 0], ![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![42, 0, 0], ![18, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![49, 0, 0], ![8, 1, 0]] ![![6, 0, 0], ![0, 1, 0]]
  ![![294, 0, 0], ![-90, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![294, 0, 0], ![0, 49, 0]], ![![48, 6, 0], ![0, 8, 5]]]
 hmul := by decide
 f := ![![![![-2303, 9152, 1840], ![-26688, 1536, 0]], ![![14112, -30576, 0], ![0, 0, 0]]], ![![![705, -2818, -570], ![8221, -468, 0]], ![![-4320, 9408, 0], ![0, 0, 0]]]]
 g := ![![![![11701, 12275510, -681980], ![38220, 40100424, 0]], ![![-885, -944270, 52460], ![-2891, -3084648, 0]]], ![![![1802, 1888540, -104920], ![5886, 6169296, 0]], ![![-60, -153719, 8540], ![-196, -502151, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![294, 0, 0], ![-90, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![49, 0, 0], ![8, 1, 0]] ![![6, 0, 0], ![18, 0, 1]]
  ![![294, 0, 0], ![144, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![294, 0, 0], ![882, 0, 49]], ![![48, 6, 0], ![174, -12, 8]]]
 hmul := by decide
 f := ![![![![-3329, 98784, 61863], ![342, 0, 0]], ![![14112, -606816, 0], ![0, 0, 0]]], ![![![-1635, 48384, 30300], ![169, 0, 0]], ![![6912, -297216, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-21, 0, 0], ![49, 0, 0]]], ![![![-3, -12, 0], ![0, 31, 0]], ![![53, 214, 0], ![8, -552, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![294, 0, 0], ![144, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![343, 0, 0], ![155, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![343, 0, 0], ![155, 1, 0]] ![![6, 0, 0], ![0, 1, 0]]
  ![![2058, 0, 0], ![498, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![2058, 0, 0], ![0, 343, 0]], ![![930, 6, 0], ![0, 155, 5]]]
 hmul := by decide
 f := ![![![![-302869, -4604136, -45010], ![13428732, -37500, 0]], ![![670222, 5231436, 0], ![0, 0, 0]]], ![![![-73289, -1113904, -10890], ![3248887, -9072, 0]], ![![162182, 1265670, 0], ![0, 0, 0]]]]
 g := ![![![![-611543, 5503831028, 55259360], ![2527224, -22744752576, 0]], ![![9379, -88771469, -891280], ![-38759, 366850848, 0]]], ![![![-276391, 2485601109, 24955840], ![1142196, -10271823744, 0]], ![![4067, -40117876, -402790], ![-16807, 165788365, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2058, 0, 0], ![498, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![343, 0, 0], ![155, 1, 0]] ![![6, 0, 0], ![18, 0, 1]]
  ![![2058, 0, 0], ![1026, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![2058, 0, 0], ![6174, 0, 343]], ![![930, 6, 0], ![2820, -12, 155]]]
 hmul := by decide
 f := ![![![![-147475, 72383976, 2343663], ![-51798, 0, 0]], ![![670222, -160183058, 0], ![0, 0, 0]]], ![![![-73524, 36086472, 1168415], ![-25823, 0, 0]], ![![334134, -79858026, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-168, 0, 0], ![343, 0, 0]]], ![![![0, -15, 0], ![0, 31, 0]], ![![-75, 30, 0], ![155, -62, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2058, 0, 0], ![1026, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2401, 0, 0], ![-531, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![2401, 0, 0], ![-531, 1, 0]] ![![6, 0, 0], ![0, 1, 0]]
  ![![14406, 0, 0], ![6672, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![14406, 0, 0], ![0, 2401, 0]], ![![-3186, 6, 0], ![0, -531, 5]]]
 hmul := by decide
 f := ![![![![-55223, -1437720358, 4105740], ![4193351046, 3421458, 0]], ![![-249704, -3340729791, 0], ![0, 0, 0]]], ![![![-25576, -665865986, 1901530], ![1942109131, 1584618, 0]], ![![-115648, -1547226009, 0], ![0, 0, 0]]]]
 g := ![![![![-391813199, 14801399809179, 11092176160], ![845992350, -31958777952192, 0]], ![![219064, -8329431519, -6242080], ![-472997, 17984680896, 0]]], ![![![86649261, -3273466586949, -2453137440], ![-187090716, 7067979592128, 0]], ![![-50040, 1842085816, 1380460], ![108045, -3977381351, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![14406, 0, 0], ![6672, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![2401, 0, 0], ![-531, 1, 0]] ![![6, 0, 0], ![18, 0, 1]]
  ![![14406, 0, 0], ![-3090, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![14406, 0, 0], ![43218, 0, 2401]], ![![-3186, 6, 0], ![-9528, -12, -531]]]
 hmul := by decide
 f := ![![![![-84992907, -41104982, -5941890], ![60238626, -19530100, 2048943]], ![![-8715630, 2401, 0], ![0, 0, 0]]], ![![![18231250, 8816871, 1274495], ![-12920789, 4189092, -439485]], ![![1873518, -80, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![518, 0, 0], ![2401, 0, 0]]], ![![![-1, 81, 0], ![0, 374, 0]], ![![-173, 6078, 0], ![-531, 28064, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![14406, 0, 0], ![-3090, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16807, 0, 0], ![-531, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![16807, 0, 0], ![-531, 1, 0]] ![![6, 0, 0], ![0, 1, 0]]
  ![![100842, 0, 0], ![49890, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![100842, 0, 0], ![0, 16807, 0]], ![![-3186, 6, 0], ![0, -531, 5]]]
 hmul := by decide
 f := ![![![![-2605085, 27715894960, -79149130], ![-80838026964, -65957604, 0]], ![![-82455142, 450810127320, 0], ![0, 0, 0]]], ![![![-1288825, 13712004518, -39157795], ![-39993346505, -32631486, 0]], ![![-40793390, 223031242980, 0], ![0, 0, 0]]]]
 g := ![![![![-338695028039, 85933899532708844, 8612337095560], ![684599799912, -173697059478092304, 0]], ![![81062935, -20568190409935, -2061354020], ![-163851443, 41574212416968, 0]]], ![![![10700706537, -2715001134111434, -272098730640], ![-21629197206, 5487796039039776, 0]], ![![-2569335, 649830720248, 65126350], ![5193363, -1313494277339, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100842, 0, 0], ![49890, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![16807, 0, 0], ![-531, 1, 0]] ![![6, 0, 0], ![18, 0, 1]]
  ![![100842, 0, 0], ![-46308, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![100842, 0, 0], ![302526, 0, 16807]], ![![-3186, 6, 0], ![-9528, -12, -531]]]
 hmul := by decide
 f := ![![![![-20424245575, -10033701175, -1454964810], ![14748930222, -4766060600, 501595116]], ![![-245550270, 16807, 0], ![0, 0, 0]]], ![![![9379088667, 4607610806, 668139370], ![-6772906733, 2188639004, -230339208]], ![![112790114, 9524, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![7721, 0, 0], ![16807, 0, 0]]], ![![![2, -3138, 0], ![0, -6829, 0]], ![![-248, 6276, 0], ![-531, 13658, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100842, 0, 0], ![-46308, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl

lemma PowJ0_6J1_0 : J0 ^ 6*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![117649, 0, 0], ![-34145, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
def MulR61_J0_6J1_1 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) J1
  ![![117649, 0, 0], ![-34145, 1, 0]] ![![6, 0, 0], ![0, 1, 0]]
  ![![705894, 0, 0], ![-151794, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![705894, 0, 0], ![0, 117649, 0]], ![![-204870, 6, 0], ![0, -34145, 5]]]
 hmul := by decide
 f := ![![![![-23696390984, -288504978937234, 12812624400], ![841472855233602, 10677187008, 0]], ![![-81647582457, -510838551991152, 0], ![0, 0, 0]]], ![![![5095623384, 62039519810396, -2755200515], ![-180948599446985, -2296000422, 0]], ![![17557328907, 109849676019160, 0], ![0, 0, 0]]]]
 g := ![![![![22093983737893, 75880515446605966798, -2499457009063320], ![102744578551692, 352870341191148641616, 0]], ![![-309330873, -1062663017766098, 35003459220], ![-1438494323, -4941746368528536, 0]]], ![![![-6412286310929, -22022628380184607119, 725411688875280], ![-29819323775424, -102412751741385380064, 0]], ![![89887347, 308414256227552, -10158973880], ![418006897, 1434231741609745, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_1 : J0 ^ 6*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![705894, 0, 0], ![-151794, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR61_J0_6J1_1]
 rfl
def MulR62_J0_6J1_2 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![117649, 0, 0], ![-34145, 1, 0]] ![![6, 0, 0], ![18, 0, 1]]
  ![![705894, 0, 0], ![-348834, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![705894, 0, 0], ![2117682, 0, 117649]], ![![-204870, 6, 0], ![-614580, -12, -34145]]]
 hmul := by decide
 f := ![![![![346640557331870, -150093006595132, -200000612325], ![8961494776632, -74723111567468, 646790925576]], ![![-311879851815, 16588509, 0], ![0, 0, 0]]], ![![![-171300524075947, 74171963336985, 98834971820], ![-4428531860153, 36926170077276, -319626835941]], ![![154122877457, -8074643, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![58142, 0, 0], ![117649, 0, 0]]], ![![![0, -3375, 0], ![0, -6829, 0]], ![![-16875, 6750, 0], ![-34145, 13658, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_2 : J0 ^ 6*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![705894, 0, 0], ![-348834, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR62_J0_6J1_2]
 rfl

lemma PowJ0_7J1_0 : J0 ^ 7*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![823543, 0, 0], ![83504, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
def MulR71_J0_7J1_1 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![823543, 0, 0], ![83504, 1, 0]] ![![6, 0, 0], ![0, 1, 0]]
  ![![4941258, 0, 0], ![-1563582, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![4941258, 0, 0], ![0, 823543, 0]], ![![501024, 6, 0], ![0, 83504, 5]]]
 hmul := by decide
 f := ![![![![-20642105295, 19128718006912856, 347368539855], ![-55792094186829162, 289473783216, 0]], ![![203579006057, -96946937192070301, 0], ![0, 0, 0]]], ![![![6531863805, -6052976622321444, -109919214155], ![17654515148437549, -91599345126, 0]], ![![-64419317803, 30677306457087136, 0], ![0, 0, 0]]]]
 g := ![![![![61113785125898833, 1049875438955602004819476, -3357276557787314930], ![193132806378961008, 3317833929875806439276388, 0]], ![![-92645100067, -1591561960727114800, 5089473915430], ![-292778595473, -5029680740081962188, 0]]], ![![![6196695877900214, 106453213305193800501106, -340414552307450980], ![19582902003375234, 336415225981122122906568, 0]], ![![-9393479462, -161378082215644612, 516052507050], ![-29685430978, -509989715776173779, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_1 : J0 ^ 7*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4941258, 0, 0], ![-1563582, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR71_J0_7J1_1]
 rfl
def MulR72_J0_7J1_2 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![823543, 0, 0], ![83504, 1, 0]] ![![6, 0, 0], ![18, 0, 1]]
  ![![4941258, 0, 0], ![-2466516, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![4941258, 0, 0], ![14823774, 0, 823543]], ![![501024, 6, 0], ![1503102, -12, 83504]]]
 hmul := by decide
 f := ![![![![6484016958443535, -2738961237397481, 1528598060620], ![112708589283318, -1364402278624576, 10156681470594]], ![![-1295249488911, 2470629, 0], ![0, 0, 0]]], ![![![-3236611319116229, 1367200764524275, -763026657200], ![-56260478364935, 681065439340344, -5069886525681]], ![![646549002354, -1015703, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![411089, 0, 0], ![823543, 0, 0]]], ![![![-2, 172773, 0], ![0, 346118, 0]], ![![41682, 65545, 0], ![83504, 131307, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_2 : J0 ^ 7*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4941258, 0, 0], ![-2466516, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR72_J0_7J1_2]
 rfl

lemma PowJ0_8J1_0 : J0 ^ 8*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5764801, 0, 0], ![-740039, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
def MulR81_J0_8J1_1 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![5764801, 0, 0], ![-740039, 1, 0]] ![![6, 0, 0], ![0, 1, 0]]
  ![![34588806, 0, 0], ![-6504840, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![34588806, 0, 0], ![0, 5764801, 0]], ![![-4440234, 6, 0], ![0, -740039, 5]]]
 hmul := by decide
 f := ![![![![-23585766688141, 10103829152851514576, -20703476806865], ![-29469501695816917512, -17252897339046, 0]], ![![-183729845845378, 40446871398776718414, 0], ![0, 0, 0]]], ![![![4435586431740, -1900146308220276112, 3893537234915], ![5542093398975805327, 3244614362436, 0]], ![![34552602088920, -7606519489272614589, 0], ![0, 0, 0]]]]
 g := ![![![![12784167071872362001, 2434453093217462911077251230, -1871262854441819380960], ![67978470603516948300, 12944949569458865771013106752, 0]], ![![-2675986014420, -509580612667621218696, 391693425716560], ![-14229275602703, -2709641582717100965472, 0]]], ![![![-1641129020010596519, -312515598136798741001936347, 240217744123451916800], ![-8726531827703162712, -1661768989848743680104668160, 0]], ![![343528189380, 65415879406439395669, -50282466137860], ![1826675198467, 347842093288801759033, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_1 : J0 ^ 8*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![34588806, 0, 0], ![-6504840, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR81_J0_8J1_1]
 rfl
def MulR82_J0_8J1_2 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![5764801, 0, 0], ![-740039, 1, 0]] ![![6, 0, 0], ![18, 0, 1]]
  ![![34588806, 0, 0], ![12357258, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![34588806, 0, 0], ![103766418, 0, 5764801]], ![![-4440234, 6, 0], ![-13320672, -12, -740039]]]
 hmul := by decide
 f := ![![![![80580233083053093015, -34311408567444858245, -2153617198227490], ![1621014227099486898, -17088700428735769468, 134007710325843654]], ![![-1763463509844288, 363182463, 0], ![0, 0, 0]]], ![![![28788236573053758698, -12258154502682595070, -769405088794750], ![579126409449894055, -6105139335616225580, 47875831576427187]], ![![-630018083380620, 132398263, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-2059540, 0, 0], ![5764801, 0, 0]]], ![![![-4, -1594753, 0], ![0, 4463833, 0]], ![![264445, 23784886, 0], ![-740039, -66575676, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_2 : J0 ^ 8*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![34588806, 0, 0], ![12357258, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR82_J0_8J1_2]
 rfl
