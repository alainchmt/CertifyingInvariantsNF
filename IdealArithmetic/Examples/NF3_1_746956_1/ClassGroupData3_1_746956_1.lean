import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_746956_1.RI3_1_746956_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![118, 4, 5]

def alpha1 := B.equivFun.symm ![-13, 3, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![9, -2, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![9, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![0, 6, 11]]]
 hmul := by decide
 f := ![![![![-113152, -111620, 5379], ![352598, 9659, 0]], ![![0, 0, 0], ![-33360, -9, 0]]], ![![![-50282, -49603, 2387], ![156687, 4293, 0]], ![![0, 0, 0], ![-14824, -4, 0]]]]
 g := ![![![![33, -223, -308], ![-9, 252, 0]], ![![7, -64, -88], ![3, 72, 0]]], ![![![7, -64, -88], ![3, 72, 0]], ![![-7, 31, 44], ![7, -35, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![4, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![27, 0, 0], ![13, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![12, 3, 0], ![3, 9, 11]]]
 hmul := by decide
 f := ![![![![1080626, -671600, -1814252], ![136343, 453563, 0]], ![![-2127024, 156672, 0], ![-98784, -27, 0]]], ![![![520276, -323348, -873488], ![65643, 218372, 0]], ![![-1024072, 75431, 0], ![-47560, -13, 0]]]]
 g := ![![![![2644, -42489, -27500], ![-297, 67500, 0]], ![![835, -13597, -8800], ![-72, 21600, 0]]], ![![![1151, -18696, -12100], ![-105, 29700, 0]], ![![248, -4148, -2684], ![-8, 6589, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![27, 0, 0], ![13, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![81, 0, 0], ![40, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0, 0], ![27, 27, 0]], ![![39, 3, 0], ![12, 18, 11]]]
 hmul := by decide
 f := ![![![![1099847388, -1801905070, -3545158496], ![-234019225, 886289624, 0]], ![![-1452822210, 725241330, 0], ![-284688, -81, 0]]], ![![![543124489, -889813242, -1750663244], ![-115562917, 437665811, 0]], ![![-717429826, 358137257, 0], ![-140584, -40, 0]]]]
 g := ![![![![25445, -1098404, -274604], ![-972, 2022084, 0]], ![![8363, -361500, -90376], ![-297, 665496, 0]]], ![![![12207, -528347, -132088], ![-402, 972648, 0]], ![![3681, -159631, -39908], ![-107, 293869, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![81, 0, 0], ![40, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![243, 0, 0], ![-41, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![243, 0, 0], ![81, 81, 0]], ![![120, 3, 0], ![39, 45, 11]]]
 hmul := by decide
 f := ![![![![70178253402, -73274627668, -100182447068], ![-1032124753, 25045611767, 0]], ![![-122971349124, 61475845536, 0], ![-749088, -243, 0]]], ![![![-11841022778, 12363467216, 16903564568], ![174148147, -4225891142, 0]], ![![20748686030, -10372684585, 0], ![126392, 41, 0]]]]
 g := ![![![![-1238, -47361, 14080], ![243, -311040, 0]], ![![-410, -15688, 4664], ![81, -103032, 0]]], ![![![-590, -23385, 6952], ![246, -153576, 0]], ![![-190, -7548, 2244], ![82, -49571, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![243, 0, 0], ![-41, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![118, 4, 5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![729, 0, 0], ![243, 243, 0]], ![![-123, 3, 0], ![-42, -36, 11]]]
 hmul := by decide
 f := ![![![![-192910161, -25928043, -414034964], ![-72946066, 103508741, 0]], ![![-1510370580, 762371380, 0], ![-516672, -118, 0]]]]
 g := ![![![![86, -18, 1]], ![![70, -9, -67]]], ![![![-14, 3, -1]], ![![-41, 8, 12]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![3, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![3, 1, 0]] ![![11, 0, 0], ![3, 1, 0]]
  ![![121, 0, 0], ![36, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![33, 11, 0]], ![![33, 11, 0], ![8, 10, 11]]]
 hmul := by decide
 f := ![![![![-335955564, 84872253, 2794197], ![-83908583, 0, 37195158]], ![![0, 0, 0], ![6370287, 0, -3872]]], ![![![-99259696, 25075916, 825559], ![-24791186, 0, 10989489]], ![![0, 0, 0], ![1882132, 0, -1144]]]]
 g := ![![![![-511669, 20328633, 5590870], ![15851, -61495346, -1452]], ![![-127931, 5082480, 1397806], ![3982, -15374810, -363]]], ![![![-127931, 5082480, 1397806], ![3982, -15374810, -363]], ![![-23280, 924321, 254211], ![771, -2796128, -66]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![36, 1, 0]] ![![11, 0, 0], ![3, 1, 0]]
  ![![-13, 3, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![363, 121, 0]], ![![396, 11, 0], ![107, 43, 11]]]
 hmul := by decide
 f := ![![![![-3024467851781706, 768934680250813, 30450840408759], ![-754951715917657, 0, 334961257458081]], ![![8586586253349, 0, 691750635], ![6570132, 0, 440]]]]
 g := ![![![![2302, 75, 99]], ![![1575, 50, 66]]], ![![![771, 25, 33]], ![![526, 17, 22]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1029, 34, 44])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![36, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![1, 1, 0]] ![![11, 0, 0], ![3, 1, 0]]
  ![![33, 0, 0], ![-8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![33, 0, 0], ![9, 3, 0]], ![![11, 11, 0], ![2, 8, 11]]]
 hmul := by decide
 f := ![![![![-389481, 98841, 4273], ![-97229, 0, 43131]], ![![1023, -96, 0], ![0, 0, 0]]], ![![![-2683, 679, 27], ![-667, 0, 297]], ![![8, 0, 0], ![0, 0, 0]]]]
 g := ![![![![4089, -1100, 0], ![-1024, -1488, -1364]], ![![1023, -275, 0], ![-253, -372, -341]]], ![![![1025, -275, 0], ![-245, -372, -341]], ![![3, 0, 0], ![12, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![33, 0, 0], ![-8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![1, 1, 0]] ![![121, 0, 0], ![36, 1, 0]]
  ![![363, 0, 0], ![157, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![363, 0, 0], ![108, 3, 0]], ![![121, 121, 0], ![35, 41, 11]]]
 hmul := by decide
 f := ![![![![-85910226675, 3408151492721, 937272828442], ![2606473947, -10309769082360, -79772880]], ![![-217074, 894, 0], ![0, 0, 0]]], ![![![-37189217076, 1475336413182, 405731005749], ![1128302534, -4462940620800, -34532454]], ![![-93968, 387, 0], ![0, 0, 0]]]]
 g := ![![![![4177, -93516, 0], ![1804, 208692, -15004]], ![![1190, -27630, 0], ![635, 61659, -4433]]], ![![![992, -23379, 0], ![572, 52173, -3751]], ![![194, -6377, 0], ![333, 14230, -1023]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![363, 0, 0], ![157, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![9, 0, 0], ![4, 1, 0]] ![![11, 0, 0], ![3, 1, 0]]
  ![![99, 0, 0], ![-41, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![99, 0, 0], ![27, 9, 0]], ![![44, 11, 0], ![11, 11, 11]]]
 hmul := by decide
 f := ![![![![19999477734, -5083931349, -205529075], ![4992227449, 0, -2214936141]], ![![-37541295, 3412836, 0], ![0, 0, 0]]], ![![![-8312142443, 2112973252, 85421578], ![-2074859452, 0, 920567274]], ![![15602837, -1418436, 0], ![0, 0, 0]]]]
 g := ![![![![3597, -7192, 0], ![-1488, -16740, -4092]], ![![903, -1798, 0], ![-363, -4185, -1023]]], ![![![1517, -2997, 0], ![-576, -6975, -1705]], ![![306, -599, 0], ![-109, -1394, -341]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![99, 0, 0], ![-41, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![9, 0, 0], ![4, 1, 0]] ![![121, 0, 0], ![36, 1, 0]]
  ![![1089, 0, 0], ![157, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1089, 0, 0], ![324, 9, 0]], ![![484, 121, 0], ![143, 44, 11]]]
 hmul := by decide
 f := ![![![![-59091992726953338, 2343077779077273686, 644356200275807389], ![1783190420718630, -7087865306897906652, -18183276024870]], ![![-30015312030, 49612077, 0], ![0, 0, 0]]], ![![![-8510584433178979, 337456233105623169, 92801877114364168], ![256819781084235, -1020813030017181222, -2618803305492]], ![![-4322884295, 7145262, 0], ![0, 0, 0]]]]
 g := ![![![![4805, -93512, 0], ![1056, 626076, -45012]], ![![1347, -27629, 0], ![816, 184977, -13299]]], ![![![1880, -38964, 0], ![1287, 260865, -18755]], ![![566, -11335, 0], ![242, 75889, -5456]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1089, 0, 0], ![157, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![13, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![27, 0, 0], ![13, 1, 0]] ![![11, 0, 0], ![3, 1, 0]]
  ![![297, 0, 0], ![-41, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![297, 0, 0], ![81, 27, 0]], ![![143, 11, 0], ![38, 20, 11]]]
 hmul := by decide
 f := ![![![![224934948373692, -57179525282863, -2266155159002], ![56147756348937, 0, -24911485453932]], ![![-398159064270, 3619627830, 0], ![0, 0, 0]]], ![![![-31081929168647, 7901173061760, 313141531125], ![-7758601313102, 0, 3442315353675]], ![![55018359410, -500166900, 0], ![0, 0, 0]]]]
 g := ![![![![4171, -7206, 0], ![-306, -50220, -12276]], ![![1067, -1802, 0], ![99, -12555, -3069]]], ![![![1978, -3403, 0], ![-84, -23715, -5797]], ![![485, -801, 0], ![122, -5579, -1364]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![297, 0, 0], ![-41, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![27, 0, 0], ![13, 1, 0]] ![![121, 0, 0], ![36, 1, 0]]
  ![![3267, 0, 0], ![-932, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3267, 0, 0], ![972, 27, 0]], ![![1573, 121, 0], ![467, 53, 11]]]
 hmul := by decide
 f := ![![![![-2572282277293417848666, 101977712826017796559359, 28044130525779660063928], ![77483891268221107571, -308484669762252943703040, -263320042438566795]], ![![-383978252002653, 137972781864, 0], ![0, 0, 0]]], ![![![733844524251510660194, -29093146896696422730485, -8000689428763846772914], ![-22105322509438338465, 88007365178740822868736, 75122381775511257]], ![![109544873885422, -39362153742, 0], ![0, 0, 0]]]]
 g := ![![![![837, -3264811, 0], ![-99, -11490336, -135036]], ![![954, -964604, 0], ![2448, -3394872, -39897]]], ![![![1077, -1541717, 0], ![2343, -5425992, -63767]], ![![422, -453446, 0], ![1058, -1595879, -18755]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3267, 0, 0], ![-932, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![40, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![81, 0, 0], ![40, 1, 0]] ![![11, 0, 0], ![3, 1, 0]]
  ![![891, 0, 0], ![-41, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![891, 0, 0], ![243, 81, 0]], ![![440, 11, 0], ![119, 47, 11]]]
 hmul := by decide
 f := ![![![![143403236690498871, -36459240428546955, -1443899223063233], ![35795497240268161, 0, -15881992240101900]], ![![-244994830960968, 601952901543, 0], ![0, 0, 0]]], ![![![-6600839571735006, 1678215935220229, 66462566321034], ![-1647663889089523, 0, 731046838801224]], ![![11277092570567, -27707844150, 0], ![0, 0, 0]]]]
 g := ![![![![4212, -7207, 0], ![-27, -150660, -36828]], ![![1067, -1802, 0], ![297, -37665, -9207]]], ![![![2077, -3537, 0], ![204, -73935, -18073]], ![![531, -868, 0], ![518, -18134, -4433]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![891, 0, 0], ![-41, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![81, 0, 0], ![40, 1, 0]] ![![121, 0, 0], ![36, 1, 0]]
  ![![9801, 0, 0], ![-932, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![9801, 0, 0], ![2916, 81, 0]], ![![4840, 121, 0], ![1439, 80, 11]]]
 hmul := by decide
 f := ![![![![-356421803834535392178, 14129511835455425336721, 3885643990629332724769], ![10729974358778109347, -42742048539578291574132, -12154088066698974]], ![![-17056486573434, 1830684321, 0], ![0, 0, 0]]], ![![![33893442657255514547, -1343626551512387874887, -369499986718107579933], ![-1020352197117267281, 4064496491641007896038, 1155776337216270]], ![![1621963200319, -174086415, 0], ![0, 0, 0]]]]
 g := ![![![![837, -3264811, 0], ![-297, -34471008, -405108]], ![![954, -964604, 0], ![7344, -10184616, -119691]]], ![![![638, -1602176, 0], ![2244, -16916328, -198803]], ![![148, -472683, 0], ![239, -4990751, -58652]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9801, 0, 0], ![-932, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![243, 0, 0], ![-41, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![243, 0, 0], ![-41, 1, 0]] ![![11, 0, 0], ![3, 1, 0]]
  ![![2673, 0, 0], ![-41, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![2673, 0, 0], ![729, 243, 0]], ![![-451, 11, 0], ![-124, -34, 11]]]
 hmul := by decide
 f := ![![![![1984960288573809, -504741562015989, -19985531518052], ![495467209427773, 0, -219837293255877]], ![![9812347776000, 7136252685, 0], ![0, 0, 0]]], ![![![-30451095143899, 7743194368423, 306596220217], ![-7600917369385, 0, 3372503909346]], ![![-150530334250, -109476603, 0], ![0, 0, 0]]]]
 g := ![![![![4253, -7208, 0], ![2592, -451980, -110484]], ![![1067, -1802, 0], ![891, -112995, -27621]]], ![![![-698, 1223, 0], ![1122, 76725, 18755]], ![![-165, 311, 0], ![1112, 19531, 4774]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2673, 0, 0], ![-41, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![243, 0, 0], ![-41, 1, 0]] ![![121, 0, 0], ![36, 1, 0]]
  ![![29403, 0, 0], ![-10733, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![29403, 0, 0], ![8748, 243, 0]], ![![-4961, 121, 0], ![-1477, -1, 11]]]
 hmul := by decide
 f := ![![![![-40703842806349935865311, 1613579608661519311755518, 443737323293505828799750], ![1225134443247286120758, -4881109210564431859984200, -462572061456199728]], ![![1876719762624366, 93434220738, 0], ![0, 0, 0]]], ![![![14858164106600927925254, -589006564776178923265319, -161977875187012835023735], ![-447212040814425768201, 1781756135848028459439600, 168853138337412672]], ![![-685060876139780, -34106386257, 0], ![0, 0, 0]]]]
 g := ![![![![-36288, -432863431, 0], ![-891, -1186266708, -1215324]], ![![-2583, -127891469, 0], ![22032, -350487891, -359073]]], ![![![10610, 73479903, 0], ![12342, 201372435, 206305]], ![![6368, 21740335, 0], ![12497, 59579614, 61039]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![29403, 0, 0], ![-10733, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl
