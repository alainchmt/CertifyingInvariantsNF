import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_116424_1.RI3_1_116424_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![10, -3, 0]

def alpha1 := B.equivFun.symm ![29, 2, 2]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-5, 1, 1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![-2, 2, 5]]]
 hmul := by decide
 f := ![![![![-15, 12, 40], ![8, -15, 0]], ![![0, 0, 0], ![-2, 0, 0]]], ![![![990, -832, -2640], ![-416, 990, 0]], ![![0, 0, 0], ![132, 1, 0]]]]
 g := ![![![![15, -33, -40], ![4, 32, 0]], ![![-17, 32, 40], ![2, -32, 0]]], ![![![-17, 32, 40], ![2, -32, 0]], ![![-33, 63, 80], ![2, -63, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![8, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![4, 2, 0], ![-2, 4, 5]]]
 hmul := by decide
 f := ![![![![-455, 389, 1170], ![196, -455, 0]], ![![-24, -24, 0], ![-4, 0, 0]]], ![![![13230, -11320, -34020], ![-5660, 13230, 0]], ![![690, 690, 0], ![130, 1, 0]]]]
 g := ![![![![107, -217, -270], ![8, 432, 0]], ![![-109, 216, 270], ![4, -432, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-144, 288, 360], ![0, -575, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![16, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![0, 8, 0]], ![![4, 2, 0], ![-2, 4, 5]]]
 hmul := by decide
 f := ![![![![-2175, 1797, 5510], ![900, -2175, 0]], ![![-112, -112, 0], ![-8, 0, 0]]], ![![![31425, -25968, -79610], ![-12984, 31425, 0]], ![![1610, 1610, 0], ![130, 1, 0]]]]
 g := ![![![![-381, 759, 950], ![16, -3040, 0]], ![![379, -760, -950], ![8, 3040, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![228, -456, -570], ![0, 1825, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![32, 0, 0], ![-14, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![0, 16, 0]], ![![4, 2, 0], ![-2, 4, 5]]]
 hmul := by decide
 f := ![![![![7905, -6427, -19890], ![-3212, 7905, 0]], ![![416, 416, 0], ![-16, 0, 0]]], ![![![-60605, 49271, 152490], ![24636, -60605, 0]], ![![-3198, -3198, 0], ![138, 1, 0]]]]
 g := ![![![![14031, 92765, -38610], ![-3232, 247104, 0]], ![![-1555, -10307, 4290], ![368, -27456, 0]]], ![![![1563, 10307, -4290], ![-350, 27456, 0]], ![![-1271, -8433, 3510], ![304, -22463, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![-14, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![64, 0, 0], ![18, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![0, 32, 0]], ![![-28, 2, 0], ![-2, -12, 5]]]
 hmul := by decide
 f := ![![![![86193, -78939, -255170], ![-39468, 101745, 0]], ![![-36288, 5184, 0], ![-32, 0, 0]]], ![![![-392571, 359504, 1162090], ![179754, -463365, 0]], ![![165186, -23598, 0], ![138, 1, 0]]]]
 g := ![![![![206353, -2133386, -533250], ![24704, 6825600, 0]], ![![-8271, 85335, 21330], ![-928, -273024, 0]]], ![![![-90811, 938689, 234630], ![-10814, -3003264, 0]], ![![-3377, 34765, 8690], ![-352, -111231, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![64, 0, 0], ![18, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![128, 0, 0], ![-46, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![128, 0, 0], ![0, 64, 0]], ![![36, 2, 0], ![-2, 20, 5]]]
 hmul := by decide
 f := ![![![![533905, 666508, 1877790], ![333254, -749935, 0]], ![![-4568960, -37760, 0], ![-64, 0, 0]]], ![![![-1139361, -1422732, -4008390], ![-711366, 1600835, 0]], ![![9751874, 80594, 0], ![138, 1, 0]]]]
 g := ![![![![403725, 9445156, -1073250], ![-71168, 27475200, 0]], ![![-16137, -377806, 42930], ![2880, -1099008, 0]]], ![![![113075, 2644643, -300510], ![-19838, 7693056, 0]], ![![-11325, -265864, 30210], ![2112, -773375, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![128, 0, 0], ![-46, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![256, 0, 0], ![82, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![256, 0, 0], ![0, 128, 0]], ![![-92, 2, 0], ![-2, -44, 5]]]
 hmul := by decide
 f := ![![![![-3436748, -4320312, 7883323], ![15053831, -3153081, 3588]], ![![-523072, 76032, 0], ![-128, 0, 0]]], ![![![3800620, 4779080, -8717896], ![-16650285, 3486885, -3966]], ![![578690, -84078, 0], ![138, 1, 0]]]]
 g := ![![![![-3075693, 135321583, 8054750], ![-456448, -412403200, 0]], ![![123013, -5412863, -322190], ![18304, 16496128, 0]]], ![![![1107157, -48715771, -2899710], ![164610, 148465152, 0]], ![![-18279, 803890, 47850], ![-2688, -2449919, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ07 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0*J0) J0
  ![![256, 0, 0], ![82, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![10, -3, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![512, 0, 0], ![0, 256, 0]], ![![164, 2, 0], ![-2, 84, 5]]]
 hmul := by decide
 f := ![![![![-17441107, 23784074, 72801270], ![11892037, -29109115, 0]], ![![-36462525, -1458501, 0], ![148, 3, 0]]]]
 g := ![![![![-649, -48, -45]], ![![-1167, -80, -75]]], ![![![-217, -16, -15]], ![![-389, -27, -25]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow9 : J0 ^ 9 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ07, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![7, 1, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![7, 1, 1]] ![![5, 0, 0], ![7, 1, 1]]
  ![![25, 0, 0], ![2, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![35, 5, 5]], ![![35, 5, 5], ![117, 6, 4]]]
 hmul := by decide
 f := ![![![![218901940, -103456747, -20948256], ![281581729, -58936879, 0]], ![![0, 0, 0], ![-36770, -90, 0]]], ![![![17026347, -8046941, -1629371], ![21901633, -4584153, 0]], ![![0, 0, 0], ![-2860, -7, 0]]]]
 g := ![![![![4176243, -739704, 229836], ![313725, -2019875, 0]], ![![5782491, -1024205, 318235], ![434380, -2796750, 0]]], ![![![5782491, -1024205, 318235], ![434380, -2796750, 0]], ![![19467819, -3448172, 1071398], ![1462367, -9415771, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![25, 0, 0], ![2, 1, 1]] ![![5, 0, 0], ![7, 1, 1]]
  ![![29, 2, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![125, 0, 0], ![175, 25, 25]], ![![10, 5, 5], ![82, 1, -1]]]
 hmul := by decide
 f := ![![![![-12815380038567, 6056814118653, 1225167641867], ![-16485135701886, 3451184277234, 0]], ![![28795207443, -23987538, 0], ![-279610, 2496, 0]]]]
 g := ![![![![-15, 6, -2]], ![![35, -9, 3]]], ![![![10, -3, 1]], ![![-14, 5, -1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![279, 21, 19])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![7, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![2, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![10, 0, 0], ![8, 4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![14, 2, 2]], ![![0, 5, 0], ![52, -4, 3]]]
 hmul := by decide
 f := ![![![![444, -208, -43], ![575, -120, 0]], ![![-6, 0, 0], ![0, 0, 0]]], ![![![-476, 224, 48], ![-611, 128, 0]], ![![4, -1, 0], ![0, 0, 0]]]]
 g := ![![![![68603, -13999, 38159], ![53110, -24150, 0]], ![![91463, -18661, 50873], ![70800, -32196, 0]]], ![![![-11383, 2319, -6329], ![-8800, 4005, 0]], ![![365808, -74631, 203464], ![283151, -128766, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![8, 4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![0, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![50, 0, 0], ![-14, -7, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![50, 0, 0], ![4, 2, 2]], ![![0, 25, 0], ![52, -9, 3]]]
 hmul := by decide
 f := ![![![![30429244263, -5389720555, 1674652805], ![2285736850, -14717357200, 0]], ![![84510, 234, 0], ![0, 0, 0]]], ![![![-9355804441, 1657128617, -514890348], ![-702774811, 4525012670, 0]], ![![-25983, -72, 0], ![0, 0, 0]]]]
 g := ![![![![784037, -13927, 270517], ![-228350, 451050, 0]], ![![5968, -103, 2058], ![-1716, 3430, 0]]], ![![![-707365, 12573, -244066], ![206075, -406950, 0]], ![![1069792, -19007, 369113], ![-311605, 615447, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![-14, -7, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![20, 0, 0], ![42, 11, 4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![20, 0, 0], ![28, 4, 4]], ![![10, 5, 0], ![66, -2, 5]]]
 hmul := by decide
 f := ![![![![1120927897, -529268637, -107325654], ![1441980210, -301786830, 0]], ![![-2232948, 1368, 0], ![0, 0, 0]]], ![![![1112803244, -525432416, -106547739], ![1431528523, -299599434, 0]], ![![-2216765, 1356, 0], ![0, 0, 0]]]]
 g := ![![![![231455, -167193, 189478], ![432060, -117400, 0]], ![![231903, -167518, 189846], ![432900, -117628, 0]]], ![![![715, -550, 610], ![1415, -380, 0]], ![![809662, -584809, 662780], ![1511274, -410653, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![42, 11, 4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![2, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![100, 0, 0], ![-206, -33, -22]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![100, 0, 0], ![8, 4, 4]], ![![50, 25, 0], ![56, -7, 5]]]
 hmul := by decide
 f := ![![![![46513688829861325, -8238579863254458, 2559849958663497], ![3493945910205275, -22496731627142650, 0]], ![![-5436293740, 148328, 0], ![0, 0, 0]]], ![![![-65722529395265640, 11640880800027463, -3616995735838587], ![-4936846949053689, 31787246783855932, 0]], ![![7681329607, -209582, 0], ![0, 0, 0]]]]
 g := ![![![![1489682693, -1005200639, 166634523], ![-2773689700, 642021700, 0]], ![![108340810, -73105594, 12118902], ![-201723140, 46692556, 0]]], ![![![677129668, -456910171, 75743096], ![-1260770225, 291828550, 0]], ![![853181624, -575705563, 95436104], ![-1588567023, 367703181, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100, 0, 0], ![-206, -33, -22]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![8, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![40, 0, 0], ![110, 25, 14]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![40, 0, 0], ![56, 8, 8]], ![![10, 5, 0], ![66, -2, 5]]]
 hmul := by decide
 f := ![![![![51347919389, -24259628731, -4914489868], ![66052263430, -13826618630, 0]], ![![-97004376, 13376, 0], ![0, 0, 0]]], ![![![76664455776, -36220576332, -7337525949], ![98618617631, -20643683426, 0]], ![![-144831339, 19966, 0], ![0, 0, 0]]]]
 g := ![![![![14196891701, -19986725035, 2715977623], ![27500341320, -5089112200, 0]], ![![19874991171, -27980489867, 3802242945], ![38499204864, -7124521504, 0]]], ![![![3548812645, -4996103710, 678915918], ![6874290665, -1272130990, 0]], ![![23425034948, -32978326636, 4481394382], ![45375880092, -8397093779, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![40, 0, 0], ![110, 25, 14]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![8, 0, 0], ![2, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![200, 0, 0], ![-690, -115, -86]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![200, 0, 0], ![16, 8, 8]], ![![50, 25, 0], ![56, -7, 5]]]
 hmul := by decide
 f := ![![![![1899140669978641785, -336378907497159678, 104517948174676697], ![142656815225392025, -918535173204061150, 0]], ![![-219727631880, 1271936, 0], ![0, 0, 0]]], ![![![-4388457846369647141, 777290844903954193, -241515869258265342], ![-329645628683744214, 2122514120062100574, 0]], ![![507737770789, -2939134, 0], ![0, 0, 0]]]]
 g := ![![![![826404561123747, -1458877888664727, -148633207543252], ![-1948328670649800, 342008992970800, 0]], ![![66110252739506, -116706502446624, -11890276721908], ![-155861314051496, 27359845320216, 0]]], ![![![206594539821085, -364707820166770, -37157114758287], ![-487066606439175, 85499516630550, 0]], ![![231395125241237, -408489071381769, -41617630507371], ![-545536384918853, 95763282882251, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![200, 0, 0], ![-690, -115, -86]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![80, 0, 0], ![-330, -60, -39]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![80, 0, 0], ![112, 16, 16]], ![![10, 5, 0], ![66, -2, 5]]]
 hmul := by decide
 f := ![![![![1507845271938, -712590109844, -144289797061], ![1939607399335, -406052746710, 0]], ![![-2776633072, -111296, 0], ![0, 0, 0]]], ![![![-3965854863973, 1874216808401, 379503390791], ![-5101452769723, 1067978452788, 0]], ![![7302953424, 292737, 0], ![0, 0, 0]]]]
 g := ![![![![25240939, -55489566, 1156749], ![-63065040, 11495840, 0]], ![![35337311, -77685142, 1619456], ![-88290768, 16094128, 0]]], ![![![3155075, -6936125, 144591], ![-7883050, 1436965, 0]], ![![20823969, -45778888, 954340], ![-52028647, 9484074, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![80, 0, 0], ![-330, -60, -39]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![16, 0, 0], ![2, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![400, 0, 0], ![1202, 191, 158]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![400, 0, 0], ![32, 16, 16]], ![![50, 25, 0], ![56, -7, 5]]]
 hmul := by decide
 f := ![![![![68109174838982766177, -12063609319703263382, 3748343357981408833], ![5116123348649747125, -32941569099422398150, 0]], ![![-7840598737360, 10524992, 0], ![0, 0, 0]]], ![![![139920162730663329463, -24782889869426545365, 7700413547206511365], ![10510313965564265010, -67673550881965323724, 0]], ![![-16107343156497, 21622022, 0], ![0, 0, 0]]]]
 g := ![![![![5269831812257, -7814673877102, -1426364686926], ![11540923768800, -1960751300000, 0]], ![![419379282088, -621900744023, -113511743986], ![918440000416, -156038845808, 0]]], ![![![655280155335, -971719952250, -177362107200], ![1435062559275, -243810706550, 0]], ![![738742117230, -1095486334080, -199952428884], ![1617844131553, -274864477671, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![400, 0, 0], ![1202, 191, 158]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![-14, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![-14, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![160, 0, 0], ![350, -15, 42]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![160, 0, 0], ![224, 32, 32]], ![![-70, 5, 0], ![-46, -18, -11]]]
 hmul := by decide
 f := ![![![![24989298051072370, -11812776689546529, -2391057263140255], ![32144250480963965, -6729654731696730, 0]], ![![6490314033664, 38179200, 0], ![0, 0, 0]]], ![![![54777517573441493, -25894067987836377, -5241290931145208], ![70461452819021782, -14751666076226262, 0]], ![![14227021915925, 83690298, 0], ![0, 0, 0]]]]
 g := ![![![![5899997506419, -2002144249326, -5256195641031], ![11714194213760, -2194938022560, 0]], ![![8259861456383, -2802956119281, -7358553581203], ![16399603756992, -3072862988672, 0]]], ![![![-2581270009467, 875945269298, 2299604390445], ![-5125001861375, 960293234550, 0]], ![![-1696173318893, 575590693421, 1511088571513], ![-3367680012232, 631016420933, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![160, 0, 0], ![350, -15, 42]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![32, 0, 0], ![-14, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![800, 0, 0], ![810, 320, 107]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![800, 0, 0], ![64, 32, 32]], ![![-350, 25, 0], ![24, -23, -11]]]
 hmul := by decide
 f := ![![![![1225290284143276944322963, -217025445904974461248067, 67433040354231961085023], ![92039526509432455539325, -592621845121773281088800, 0]], ![![19224552462472640, 22620313984, 0], ![0, 0, 0]]], ![![![1216699846147485938474223, -215503893289498425400324, 66960271281035779992406], ![91394242811460369261622, -588467008279147536727432, 0]], ![![19089770257747028, 22461724295, 0], ![0, 0, 0]]]]
 g := ![![![![171522661073, -59749816144, 68418486472], ![158917740800, -51759731200, 0]], ![![13721729420, -4779956224, 5473445627], ![12713341952, -4140753312, 0]]], ![![![-75041229579, 26140567212, -29933113860], ![-69526571850, 22644902075, 0]], ![![5145739559, -1792515481, 2052578487], ![4767588053, -1552810037, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![800, 0, 0], ![810, 320, 107]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl

lemma PowJ0_6J1_0 : J0 ^ 6*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64, 0, 0], ![18, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
def MulR61_J0_6J1_1 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) J1
  ![![64, 0, 0], ![18, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![320, 0, 0], ![-1082, -66, -133]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![320, 0, 0], ![448, 64, 64]], ![![90, 5, 0], ![178, 14, 21]]]
 hmul := by decide
 f := ![![![![23540843582113181922, -11127925003355809188, -2252392032132949229], ![30281117607860703015, -6339719149188476790, 0]], ![![-4725623212265408, 945852160, 0], ![0, 0, 0]]], ![![![-79517015948109707858, 37588261732198375966, 7608201996490791958], ![-102284529581615757410, 21414506533469939016, 0]], ![![15962361545105450, -3194929741, 0], ![0, 0, 0]]]]
 g := ![![![![114316300579, -147652260151, -117266535904], ![-307339806720, 52357856320, 0]], ![![159611437899, -206155985675, -163730634915], ![-429115956224, 73103421952, 0]]], ![![![32117758459, -41483668610, -32946641674], ![-86348713280, 14710211415, 0]], ![![63494077701, -82009686790, -65132710230], ![-170704066769, 29080837604, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_1 : J0 ^ 6*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![320, 0, 0], ![-1082, -66, -133]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR61_J0_6J1_1]
 rfl
def MulR62_J0_6J1_2 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![64, 0, 0], ![18, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![1600, 0, 0], ![-6386, -1148, -787]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1600, 0, 0], ![128, 64, 64]], ![![450, 25, 0], ![88, 9, 21]]]
 hmul := by decide
 f := ![![![![4473915764618744920729648017, -792427374813251084479313454, 246218995837299731135609921], ![336064926010461539524623725, -2163846607314318541787047750, 0]], ![![-55060619605530376000, 413412491008, 0], ![0, 0, 0]]], ![![![-17803458587382094982516087284, 3153378090523317324718716992, -979801571250576400113559418], ![-1337333626219657961617080664, 8610790969161357059200071252, 0]], ![![219107715146307552592, -1645129803599, 0], ![0, 0, 0]]]]
 g := ![![![![12699939294307837235, -27191090446878667103, -1082796075819478864], ![-30646424992976982400, 5373562829611550400, 0]], ![![1015287626035035720, -2173772411769612802, -86563363164383765], ![-2450006677711132160, 429585663537121216, 0]]], ![![![3571581552496991919, -7646902460067373505, -304512832690964883], ![-8618640106725383850, 1511197607222115525, 0]], ![![698397166537100026, -1495296952455946350, -59545301262089733], ![-1685313282495761433, 295503857730393825, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_2 : J0 ^ 6*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1600, 0, 0], ![-6386, -1148, -787]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR62_J0_6J1_2]
 rfl

lemma PowJ0_7J1_0 : J0 ^ 7*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![128, 0, 0], ![-46, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
def MulR71_J0_7J1_1 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![128, 0, 0], ![-46, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![640, 0, 0], ![-1830, -200, -197]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![640, 0, 0], ![896, 128, 128]], ![![-230, 5, 0], ![-270, -50, -43]]]
 hmul := by decide
 f := ![![![![43253723828720418875, -20446590199618866450, -4138449119423955040], ![55638205496400022130, -11648653299860483610, 0]], ![![3387005516032000, 1542163968, 0], ![0, 0, 0]]], ![![![-123581709956285210845, 58418659851120474012, 11824106076293525246], ![-158965840753316495328, 33281770124236483058, 0]], ![![-9677130574007908, -4406169997, 0], ![0, 0, 0]]]]
 g := ![![![![393573685, -403598468, -110451614], ![-965251840, 197137920, 0]], ![![551002437, -565036484, -154631841], ![-1351349248, 275992448, 0]]], ![![![-141439885, 145043328, 39693639], ![346887750, -70846465, 0]], ![![-166036732, 170267774, 46596814], ![407214979, -83167310, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_1 : J0 ^ 7*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![640, 0, 0], ![-1830, -200, -197]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR71_J0_7J1_1]
 rfl
def MulR72_J0_7J1_2 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![128, 0, 0], ![-46, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![3200, 0, 0], ![10950, 2505, 1454]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3200, 0, 0], ![256, 128, 128]], ![![-1150, 25, 0], ![-40, -55, -43]]]
 hmul := by decide
 f := ![![![![3773673539712671170272381367, -668399313433162248315429838, 207681628389356738562483337], ![283465175775261473231672650, -1825168628503060514293129650, 0]], ![![18054472884067715840, 1644119688064, 0], ![0, 0, 0]]], ![![![12892014098199196021227675207, -2283454909738454322358268718, 709503472665633462094545097], ![968403070373022847287665091, -6235329962337954961606366566, 0]], ![![61679558792644900281, 5616811834566, 0], ![0, 0, 0]]]]
 g := ![![![![387806679491719994137, -729715454580314909597, 45549864692612342911], ![776492321866782332800, -132554788708605699200, 0]], ![![31024523228946599792, -58377215422953207405, 3643987868088018436], ![62119363463333584384, -10604379292250045824, 0]]], ![![![-139368027616241133827, 262241495580322102497, -16369482879243660373], ![-279051932523610565475, 47636877935209470250, 0]], ![![-4847578711056737624, 9121434183106026839, -569372746918189688], ![-9706144447315508197, 1656933224137980235, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_2 : J0 ^ 7*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3200, 0, 0], ![10950, 2505, 1454]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR72_J0_7J1_2]
 rfl

lemma PowJ0_8J1_0 : J0 ^ 8*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![256, 0, 0], ![82, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
def MulR81_J0_8J1_1 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![256, 0, 0], ![82, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![1280, 0, 0], ![-3430, -345, -494]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![1280, 0, 0], ![1792, 256, 256]], ![![410, 5, 0], ![626, 78, 85]]]
 hmul := by decide
 f := ![![![![55536536455761663483850, -26252851643852943621708, -5313605027387979578805], ![71437859703818144237295, -14956611522292950342390, 0]], ![![-2435775251772817152, 6191963136, 0], ![0, 0, 0]]], ![![![-148712892964239047363775, 70298541566923973856023, 14228499400959875189485], ![-191292641956357896500173, 40050048317186713248108, 0]], ![![6522394218630707091, -16580521758, 0], ![0, 0, 0]]]]
 g := ![![![![5563230136274406100157, -6479289975214574471887, -3502464231908329703189], ![-11809614840163648318720, 1832829734325889076480, 0]], ![![7788521872099107142781, -9071005594139608650120, -4903449724035879595425], ![-16533460099725037494528, 2565961523064101275648, 0]]], ![![![1781972146801078118830, -2075397562936684118700, -1121883070364469253126], ![-3782767240276948522665, 587078272225633549790, 0]], ![![2720767141422347062097, -3168777640415322883489, -1712923852286452653573], ![-5775639551645200323892, 896368259953961415779, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_1 : J0 ^ 8*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1280, 0, 0], ![-3430, -345, -494]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR81_J0_8J1_1]
 rfl
def MulR82_J0_8J1_2 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![256, 0, 0], ![82, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![6400, 0, 0], ![21878, 4814, 2739]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![6400, 0, 0], ![512, 256, 256]], ![![2050, 25, 0], ![216, 73, 85]]]
 hmul := by decide
 f := ![![![![37995553570480808899886064451133, -6729835442087445397060748413329, 2091060172835918687690567845961], ![2854093274868403643616077933400, -18376865865255456946958858105100, 0]], ![![-102209344754328928853760, 10232422876928, 0], ![0, 0, 0]]], ![![![129682012952748508066046525534569, -22969493136920393058605193909018, 7136963853301022598972259614902], ![9741259864875105826898404671019, -62721785399133556939419229010600, 0]], ![![-348849071135012080060526, 34924117991919, 0], ![0, 0, 0]]]]
 g := ![![![![325663684552665993, -599183539989221984, 65648178221924252], ![690657951450803200, -124347056241612800, 0]], ![![26048771316677764, -47926728555394918, 5250982725349545], ![55243467075887104, -9946113692076800, 0]]], ![![![104313726746592577, -191925200832122094, 21027846976122521], ![221225479660008800, -39829755240745925, 0]], ![![10989916495564733, -20220176158256636, 2215377492077567], ![23307091252351863, -4196242410148891, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_2 : J0 ^ 8*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6400, 0, 0], ![21878, 4814, 2739]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR82_J0_8J1_2]
 rfl
