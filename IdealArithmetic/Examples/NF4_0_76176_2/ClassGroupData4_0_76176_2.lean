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
 M := ![![![4, 0, 0, 0], ![0, -2, 0, 0]], ![![0, -2, 0, 0], ![0, 0, 1, 0]]]
 hmul := by decide
 f := ![![![![-33013, 49602, 26208, -72345], ![37203, -13104, -4095, 0]], ![![0, 0, 0, 0], ![1269, 72, 3, 0]]], ![![![-24, 36, 20, -53], ![27, -8, -3, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]]]]
 g := ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![4, 0, 0, -1], ![0, -2, 0, 0]]], ![![![4, 0, 0, -1], ![0, -2, 0, 0]], ![![0, 0, 0, 1], ![1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0], ![0, 0, 1, -2]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![4, 0, 0, 0], ![0, 1, 0, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0], ![0, -2, 0, 0]], ![![0, 0, 2, -4], ![-4, -1, 0, 1]]]
 hmul := by decide
 f := ![![![![514, -648, -356, 954], ![-486, 179, 54, 0]], ![![0, 0, 0, 0], ![72, -6, 0, 0]]], ![![![-1, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, 0, 0], ![-1, 0, 0, 0]]]]
 g := ![![![![13699, -14904, -20454, 37635], ![-13134, 9096, -6, 0]], ![![-20169, 21942, 30114, -55409], ![19339, -13392, 9, 0]]], ![![![13437, -14619, -20062, 36914], ![-12882, 8922, -6, 0]], ![![-27145, 29532, 40530, -74574], ![26027, -18024, 12, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0], ![0, 1, 0, -1]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![4, 0, 0, 0], ![-2, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0], ![0, -4, 0, 0]], ![![0, 2, 0, -2], ![6, -8, -9, 18]]]
 hmul := by decide
 f := ![![![![-5489649, 8190336, 4403284, -11992992], ![6142752, -2201642, -682528, 0]], ![![156148, -18725, 0, 0], ![1605, -36, 3, 0]]], ![![![5499896, -8205624, -4411503, 12015378], ![-6154218, 2205752, 683802, 0]], ![![-156440, 18760, 0, 0], ![-1608, 36, -3, 0]]]]
 g := ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![-4, 0, 0, 1], ![0, 4, 0, 0]]], ![![![2, 0, 0, -1], ![0, -2, 0, 0]], ![![-5, 0, -3, 8], ![3, 8, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0], ![-2, 0, 1, -2]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![8, 0, 0, 0], ![-4, 3, 0, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0, 0], ![0, -4, 0, 0]], ![![-4, 0, 2, -4], ![-4, 1, 0, 1]]]
 hmul := by decide
 f := ![![![![11984, -17976, -9620, 26322], ![-13482, 4811, 1498, 0]], ![![124, 0, 0, 0], ![-144, -12, 0, 0]]], ![![![-6216, 9324, 4990, -13653], ![6993, -2495, -777, 0]], ![![-65, 0, 0, 0], ![75, 6, 0, 0]]]]
 g := ![![![![-640839, 391594, 1957917, -3097089], ![854414, -1423904, 14, 0]], ![![323303, -197560, -987753, 1562457], ![-431035, 718348, -7, 0]]], ![![![-2604, 1591, 7956, -12585], ![3472, -5786, 0, 0]], ![![320352, -195756, -978744, 1548206], ![-427108, 711796, -7, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![8, 0, 0, 0], ![-4, 3, 0, -1]] ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![![-2, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![16, 0, 0, 0], ![0, -8, 0, 0]], ![![-8, 6, 0, -2], ![6, -4, -11, 18]]]
 hmul := by decide
 f := ![![![![-277259225, 416192840, 223594635, -610403275], ![312144630, -111797316, -34813875, 0]], ![![3575350, -713575, 0, 0], ![1725, 0, 14, 0]]]]
 g := ![![![![-2, 0, -2, 4]], ![![4, 2, 0, -1]]], ![![![-2, 0, 2, -3]], ![![-7, 4, 4, -8]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![-4, 4, -1, -1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![6, 0, 0, 0], ![-4, 4, -1, -1]] ![![6, 0, 0, 0], ![-4, 4, -1, -1]]
  ![![0, 0, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![36, 0, 0, 0], ![-24, 24, -6, -6]], ![![-24, 24, -6, -6], ![-256, 80, 115, -232]]]
 hmul := by decide
 f := ![![![![1523803724377733666738360, -1115639879562883018729025, -4176848776080472568476050, 6843501284350605993639641], ![-2204071154005433361172181, 816322170115342881218772, -147843736715976059, 0]], ![![0, 0, 0, 0], ![1519191128027, -2142256, -6, 0]]]]
 g := ![![![![-6, 0, 6, -12]], ![![26, -18, -16, 31]]], ![![![26, -18, -16, 31]], ![![-19, -2, -44, 75]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
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

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![-4, 4, -1, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, -1, 0, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0, 0], ![0, -1, 0, 0]] ![![6, 0, 0, 0], ![-4, 4, -1, -1]]
  ![![6, 0, 0, 0], ![-2, 0, -3, 4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![12, 0, 0, 0], ![-8, 8, -2, -2]], ![![0, -6, 0, 0], ![22, -19, -28, 53]]]
 hmul := by decide
 f := ![![![![313054092621307, -229195592686878, -858090169543977, 1405925949532322], ![-452805753536844, 167704772348760, -327522462, 0]], ![![0, 0, 0, 0], ![-24921, 126, 3, 0]]], ![![![201240896663272, -147334047599792, -551607020023405, 903772879494985], ![-291077606087306, 107805837897158, -210541614, 0]], ![![0, 0, 0, 0], ![-16020, 81, 2, 0]]]]
 g := ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![-328, 16, -13, 53], ![160, -8, 36, 0]]], ![![![224, -12, 12, -39], ![-96, 6, -24, 0]], ![![257, -38, -16, 32], ![-48, 19, -20, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![-2, 0, -3, 4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, 0, 1, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![2, 0, 0, 0], ![0, 0, 1, -2]] ![![6, 0, 0, 0], ![-4, 4, -1, -1]]
  ![![12, 0, 0, 0], ![-10, 6, 3, -10]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![12, 0, 0, 0], ![-8, 8, -2, -2]], ![![0, 0, 6, -12], ![22, -14, -17, 30]]]
 hmul := by decide
 f := ![![![![190764623133, -139664076886, -522891256361, 856723934372], ![-275924579676, 102193641444, -199581, 0]], ![![0, 0, 0, 0], ![-18, 0, 0, 0]]], ![![![-9027769133259, 6609480424762, 24745371897329, -40543711740167], ![13057889679164, -4836224802593, 9444997, 0]], ![![0, 0, 0, 0], ![843, -6, 0, 0]]]]
 g := ![![![![-290406363, -127202715, -495968149, 777259030], ![-593303922, 203479452, -40566, 0]], ![![-97825146, -42849005, -167069880, 261824419], ![-199858027, 68543288, -13665, 0]]], ![![![95699475, 41917923, 163439562, -256135146], ![195515250, -67053888, 13368, 0]], ![![-349954354, -153285697, -597666686, 936636410], ![-714961223, 245203024, -48884, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0, 0], ![-10, 6, 3, -10]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0], ![0, 1, 0, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![4, 0, 0, 0], ![0, 1, 0, -1]] ![![6, 0, 0, 0], ![-4, 4, -1, -1]]
  ![![12, 0, 0, 0], ![0, -1, 2, -5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![24, 0, 0, 0], ![-16, 16, -4, -4]], ![![0, 6, 0, -6], ![-76, 21, 22, -51]]]
 hmul := by decide
 f := ![![![![-2831750449760444852, 2073236550332403552, 7762003718106464132, -12717549495825508853], ![4095915629681739726, -1517003694666588033, 645650759373, 0]], ![![-205523325, -2840775, 0, 0], ![-29925, -13950, -27, 0]]], ![![![314403799556511076, -230187461913914090, -861800326137808902, 1412005031330986386], ![-454761625179146350, 168429999043449942, -71685360534, 0]], ![![22818858, 315406, 0, 0], ![3322, 1548, 3, 0]]]]
 g := ![![![![143814, 762812, 417938, -1224460], ![516294, -863232, -90, 0]], ![![179938, 954418, 522914, -1532027], ![645970, -1080076, -110, 0]]], ![![![97350, 516359, 282908, -828858], ![349482, -584340, -60, 0]], ![![-203863, -1081320, -592453, 1735737], ![-731851, 1223660, 130, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0, 0], ![0, -1, 2, -5]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0], ![-2, 0, 1, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![4, 0, 0, 0], ![-2, 0, 1, -2]] ![![6, 0, 0, 0], ![-4, 4, -1, -1]]
  ![![24, 0, 0, 0], ![-28, 19, 0, -9]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![24, 0, 0, 0], ![-16, 16, -4, -4]], ![![-12, 0, 6, -12], ![30, -22, -15, 32]]]
 hmul := by decide
 f := ![![![![674861152639615, -494092552580240, -1849836300507837, 3030839144785672], ![-976136277526206, 361531455574698, -153870279, 0]], ![![51828, -1188, 0, 0], ![-36, 0, 0, 0]]], ![![![-26432104229711451, 19351989365283925, 72452038040242154, -118708057005683218], ![38232065557570439, -14160004733851946, 6026595599, 0]], ![![-2029930, 46530, 0, 0], ![1410, -19, 0, 0]]]]
 g := ![![![![-1451328158648481, -1093041328393376, -25701047482285767, 40384852634025693], ![-14316427937647770, 6778298232038880, -3959658, 0]], ![![345437513416975, 260159961957714, 6117228472132284, -9612190730591850], ![3407521061535377, -1613334980459888, 942457, 0]]], ![![![829272568268556, 624551507678668, 14685289144168632, -23075450071989138], ![8180245724261568, -3873043287885678, 2262504, 0]], ![![-1312778863717861, -988695454252830, -23247527934394203, 36529561310020482], ![-12949727384870324, 6131216153955923, -3581654, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0, 0], ![-28, 19, 0, -9]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0, 0], ![-4, 3, 0, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![8, 0, 0, 0], ![-4, 3, 0, -1]] ![![6, 0, 0, 0], ![-4, 4, -1, -1]]
  ![![24, 0, 0, 0], ![18, -16, -13, 34]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![48, 0, 0, 0], ![-32, 32, -8, -8]], ![![-24, 18, 0, -6], ![-104, 43, 82, -153]]]
 hmul := by decide
 f := ![![![![-5698353773526584491822812, 4172004620920068982893757, 15619582208503682374910942, -25591693056562683761814551], ![8242257404307602547628323, -3052686940164659752939182, 304420795740062952, 0]], ![![-21311530830630, -4838376702, 0, 0], ![-254403, 2232, -63, 0]]], ![![![-1219085973626697567141148, 892544148258768294365448, 3341599054933987235915638, -5474997742603698158073958], ![1763319862535262394697460, -653081219336965172970664, 65126725527487524, 0]], ![![-4559314732760, -1035105472, 0, 0], ![-54428, 477, -14, 0]]]]
 g := ![![![![-489028134, -105795046, -362983558, 498060212], ![605960406, -207363720, 198, 0]], ![![-1900175824, -411079034, -1410414999, 1935271153], ![2354529794, -805735928, 770, 0]]], ![![![-977178072, -211400118, -725315289, 995226045], ![1210832628, -414355062, 396, 0]], ![![-1302376757, -281752765, -966695662, 1326431042], ![1613790070, -552249817, 528, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0, 0], ![18, -16, -13, 34]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
