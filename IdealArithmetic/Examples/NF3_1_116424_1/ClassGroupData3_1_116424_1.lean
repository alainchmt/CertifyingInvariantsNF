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
  ![![10, 0, 0], ![-20, 0, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![14, 2, 2]], ![![0, 5, 0], ![52, -4, 3]]]
 hmul := by decide
 f := ![![![![444, -208, -43], ![575, -120, 0]], ![![-6, 0, 0], ![0, 0, 0]]], ![![![1600, -756, -162], ![2067, -432, 0]], ![![-12, 3, 0], ![0, 0, 0]]]]
 g := ![![![![27409, -14706, -19341], ![-48990, 7740, 0]], ![![38297, -20554, -27034], ![-68478, 10818, 0]]], ![![![-149, 86, 114], ![290, -45, 0]], ![![142620, -76540, -100668], ![-254993, 40284, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-20, 0, -3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![0, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![50, 0, 0], ![22, 21, 4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![50, 0, 0], ![4, 2, 2]], ![![0, 25, 0], ![52, -9, 3]]]
 hmul := by decide
 f := ![![![![30429244263, -5389720555, 1674652805], ![2285736850, -14717357200, 0]], ![![84510, 234, 0], ![0, 0, 0]]], ![![![16362336609, -2898146966, 900490089], ![1229080676, -7913780258, 0]], ![![45441, 126, 0], ![0, 0, 0]]]]
 g := ![![![![8837419, -927771, 5578690], ![3945150, -3038300, 0]], ![![642788, -67493, 405770], ![286980, -220994, 0]]], ![![![-798889, 83846, -504295], ![-356575, 274650, 0]], ![![9478094, -995016, 5983115], ![4231119, -3258559, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![22, 21, 4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![20, 0, 0], ![-66, -8, -9]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![20, 0, 0], ![28, 4, 4]], ![![10, 5, 0], ![66, -2, 5]]]
 hmul := by decide
 f := ![![![![1120927897, -529268637, -107325654], ![1441980210, -301786830, 0]], ![![-2232948, 1368, 0], ![0, 0, 0]]], ![![![-2781459129, 1313321821, 266316784], ![-3578115050, 748850778, 0]], ![![5540816, -3393, 0], ![0, 0, 0]]]]
 g := ![![![![1051365, -1684273, -685781], ![-2487020, 393980, 0]], ![![1445455, -2315627, -942849], ![-3419288, 541664, 0]]], ![![![492896, -789572, -321486], ![-1165890, 184695, 0]], ![![3482263, -5578756, -2271498], ![-8237681, 1304962, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![-66, -8, -9]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![2, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![100, 0, 0], ![114, 37, 16]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![100, 0, 0], ![8, 4, 4]], ![![50, 25, 0], ![56, -7, 5]]]
 hmul := by decide
 f := ![![![![46513688829861325, -8238579863254458, 2559849958663497], ![3493945910205275, -22496731627142650, 0]], ![![-5436293740, 148328, 0], ![0, 0, 0]]], ![![![19292303038666152, -3417083945148617, 1061739078934293], ![1449170448444735, -9330882474574852, 0]], ![![-2254790555, 61520, 0], ![0, 0, 0]]]]
 g := ![![![![15076250457, -6520607632, 3855379620], ![15391161600, -4129389200, 0]], ![![1176684494, -508926206, 300908080], ![1201263132, -322294236, 0]]], ![![![7354287498, -3180792436, 1880677842], ![7507903125, -2014341400, 0]], ![![8494173082, -3673802684, 2172175490], ![8671598409, -2326556363, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100, 0, 0], ![114, 37, 16]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![8, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![40, 0, 0], ![106, 18, 13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![40, 0, 0], ![56, 8, 8]], ![![10, 5, 0], ![66, -2, 5]]]
 hmul := by decide
 f := ![![![![51347919389, -24259628731, -4914489868], ![66052263430, -13826618630, 0]], ![![-97004376, 13376, 0], ![0, 0, 0]]], ![![![89523071777, -42295705645, -8568219205], ![115159515521, -24106164120, 0]], ![![-169123306, 23317, 0], ![0, 0, 0]]]]
 g := ![![![![100002661, -120601845, -5097903], ![209079480, -39283080, 0]], ![![138464451, -166986331, -7058607], ![289493216, -54391680, 0]]], ![![![24039032, -28990864, -1225469], ![50259560, -9443055, 0]], ![![165388530, -199456340, -8431126], ![345784329, -64967988, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![40, 0, 0], ![106, 18, 13]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl
def MulR32_J0_3J1_2 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) (J1*J1)
  ![![8, 0, 0], ![2, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![200, 0, 0], ![-214, 13, -36]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![200, 0, 0], ![16, 8, 8]], ![![50, 25, 0], ![56, -7, 5]]]
 hmul := by decide
 f := ![![![![1899140669978641785, -336378907497159678, 104517948174676697], ![142656815225392025, -918535173204061150, 0]], ![![-219727631880, 1271936, 0], ![0, 0, 0]]], ![![![-2276126353424224341, 403151229497362681, -125265105427332234], ![-170974663311136710, 1100867433006087206, 0]], ![![263344291133, -1524420, 0], ![0, 0, 0]]]]
 g := ![![![![332116431855, -76864727938, -109750323545], ![-340605730800, 70717214600, 0]], ![![25921301826, -5999202750, -8565885290], ![-26583881704, 5519396472, 0]]], ![![![81004091305, -18747513945, -26768399180], ![-83074654075, 17248118900, 0]], ![![93559601039, -21653349808, -30917459928], ![-95951097819, 19921550833, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_2 : J0 ^ 3*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![200, 0, 0], ![-214, 13, -36]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR32_J0_3J1_2]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![80, 0, 0], ![-234, 3, -32]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![80, 0, 0], ![112, 16, 16]], ![![10, 5, 0], ![66, -2, 5]]]
 hmul := by decide
 f := ![![![![1507845271938, -712590109844, -144289797061], ![1939607399335, -406052746710, 0]], ![![-2776633072, -111296, 0], ![0, 0, 0]]], ![![![-4530047617532, 2140847731162, 433492523121], ![-5827198613687, 1219911825210, 0]], ![![8341890423, 334368, 0], ![0, 0, 0]]]]
 g := ![![![![875422105, -687315323, -1169617151], ![-2118536560, 326281040, 0]], ![![875473031, -687355263, -1169685109], ![-2118659648, 326300000, 0]]], ![![![17105, -13315, -22635], ![-40985, 6320, 0]], ![![765986397, -601394749, -1023404543], ![-1853700546, 285492987, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![80, 0, 0], ![-234, 3, -32]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl
def MulR42_J0_4J1_2 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) (J1*J1)
  ![![16, 0, 0], ![2, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![400, 0, 0], ![722, 221, 84]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![400, 0, 0], ![32, 16, 16]], ![![50, 25, 0], ![56, -7, 5]]]
 hmul := by decide
 f := ![![![![68109174838982766177, -12063609319703263382, 3748343357981408833], ![5116123348649747125, -32941569099422398150, 0]], ![![-7840598737360, 10524992, 0], ![0, 0, 0]]], ![![![48029427980171148422, -8507051456303666056, 2643267779748214879], ![3607802891351473832, -23229832461704943486, 0]], ![![-5529056448971, 7422036, 0], ![0, 0, 0]]]]
 g := ![![![![1342448594493, -1022318703369, 715196825689], ![2008479963600, -485369314000, 0]], ![![105635351662, -80444790936, 56277811162], ![158044404560, -38193014352, 0]]], ![![![165055265422, -125695006584, 87934094739], ![246944422925, -59676594900, 0]], ![![188713023779, -143711167173, 100537894980], ![282339547189, -68230181383, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_2 : J0 ^ 4*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![400, 0, 0], ![722, 221, 84]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR42_J0_4J1_2]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![-14, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![-14, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![160, 0, 0], ![54, 57, 6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![160, 0, 0], ![224, 32, 32]], ![![-70, 5, 0], ![-46, -18, -11]]]
 hmul := by decide
 f := ![![![![24989298051072370, -11812776689546529, -2391057263140255], ![32144250480963965, -6729654731696730, 0]], ![![6490314033664, 38179200, 0], ![0, 0, 0]]], ![![![7999501286891959, -3781471657853939, -765418284836618], ![10289923813110640, -2154277466158614, 0]], ![![2077660419213, 12221814, 0], ![0, 0, 0]]]]
 g := ![![![![150425011, 48289395, 226230162], ![76455200, -134269440, 0]], ![![205128575, 65850302, 308501060], ![104258976, -183097888, 0]]], ![![![-66664207, -21400537, -100258932], ![-33882775, 59504490, 0]], ![![-40173595, -12896541, -60418622], ![-20418564, 35858941, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![160, 0, 0], ![54, 57, 6]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
def MulR52_J0_5J1_2 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) (J1*J1)
  ![![32, 0, 0], ![-14, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![800, 0, 0], ![46, 128, -23]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![800, 0, 0], ![64, 32, 32]], ![![-350, 25, 0], ![24, -23, -11]]]
 hmul := by decide
 f := ![![![![1225290284143276944322963, -217025445904974461248067, 67433040354231961085023], ![92039526509432455539325, -592621845121773281088800, 0]], ![![19224552462472640, 22620313984, 0], ![0, 0, 0]]], ![![![60891678061858711482071, -10785234939259309779317, 3351133227056650169713], ![4573970176460590534203, -29450766950960411973464, 0]], ![![955377900712476, 1124132701, 0], ![0, 0, 0]]]]
 g := ![![![![47736668552397, -19206988012007, -21859991386981], ![300215112800, 25502766847200, 0]], ![![3813744715806, -1534471324878, -1746423224908], ![23984577120, 2037449307872, 0]]], ![![![-20888846216903, 8404688283345, 9565602548999], ![-131369605150, -11159626151775, 0]], ![![1435829483771, -577710186369, -657507553421], ![9029908143, 767075409073, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_2 : J0 ^ 5*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![800, 0, 0], ![46, 128, -23]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR52_J0_5J1_2]
 rfl

lemma PowJ0_6J1_0 : J0 ^ 6*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![64, 0, 0], ![18, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
def MulR61_J0_6J1_1 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) J1
  ![![64, 0, 0], ![18, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![320, 0, 0], ![558, 179, 84]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![320, 0, 0], ![448, 64, 64]], ![![90, 5, 0], ![178, 14, 21]]]
 hmul := by decide
 f := ![![![![23540843582113181922, -11127925003355809188, -2252392032132949229], ![30281117607860703015, -6339719149188476790, 0]], ![![-4725623212265408, 945852160, 0], ![0, 0, 0]]], ![![![40831558766736585899, -19301369644697024799, -3906770685806920424], ![52522554207330431226, -10996233592978893450, 0]], ![![-8196586550860921, 1640579188, 0], ![0, 0, 0]]]]
 g := ![![![![96956270548105, -84745538843133, 22087273241319], ![127460870205120, -24449299222080, 0]], ![![135354793517761, -118308128466500, 30834708183873], ![177940422735296, -34132189998080, 0]]], ![![![27238952250365, -23808462030587, 6205211666656], ![35808932600935, -6868800648980, 0]], ![![53847928710055, -47066287805197, 12266910723520], ![70789685013162, -13578741365381, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_1 : J0 ^ 6*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![320, 0, 0], ![558, 179, 84]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR61_J0_6J1_1]
 rfl
def MulR62_J0_6J1_2 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![64, 0, 0], ![18, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![1600, 0, 0], ![-1302, -201, -166]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1600, 0, 0], ![128, 64, 64]], ![![450, 25, 0], ![88, 9, 21]]]
 hmul := by decide
 f := ![![![![4473915764618744920729648017, -792427374813251084479313454, 246218995837299731135609921], ![336064926010461539524623725, -2163846607314318541787047750, 0]], ![![-55060619605530376000, 413412491008, 0], ![0, 0, 0]]], ![![![-3631359213305428899427640460, 643192362082560143164343468, -199849453155893971938376927], ![-272775020707367665105172554, 1756337116534905872982466470, 0]], ![![44691250084787196967, -335555995486, 0], ![0, 0, 0]]]]
 g := ![![![![142125606135523, -26608458028994, 6675437025997], ![-113004601043200, 43743630036800, 0]], ![![11324749496528, -2120195859181, 531907333012], ![-9004350681344, 3485548210880, 0]]], ![![![39955131805692, -7480316014866, 1876635558403], ![-31768474746525, 12297449779150, 0]], ![![7810538166805, -1462272581360, 366849838656], ![-6210188109443, 2403939031229, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_2 : J0 ^ 6*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1600, 0, 0], ![-1302, -201, -166]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR62_J0_6J1_2]
 rfl

lemma PowJ0_7J1_0 : J0 ^ 7*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![128, 0, 0], ![-46, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
def MulR71_J0_7J1_1 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![128, 0, 0], ![-46, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![640, 0, 0], ![-2094, -387, -292]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![640, 0, 0], ![896, 128, 128]], ![![-230, 5, 0], ![-270, -50, -43]]]
 hmul := by decide
 f := ![![![![43253723828720418875, -20446590199618866450, -4138449119423955040], ![55638205496400022130, -11648653299860483610, 0]], ![![3387005516032000, 1542163968, 0], ![0, 0, 0]]], ![![![-141333581063833764567, 66810197080372654761, 13522577533781794728], ![-181800458566536380494, 38062523632870534930, 0]], ![![-11067200145803543, -5039093444, 0], ![0, 0, 0]]]]
 g := ![![![![2418229101851089, -4243637652919556, -600943066767948], ![-5071888425152000, 811538014369280, 0]], ![![3380176590492485, -5931714510404787, -839992242651160], ![-7089435203293184, 1134359766147200, 0]]], ![![![-869259839407709, 1525423617582956, 216015791602938], ![1823147738391465, -291716530706460, 0]], ![![-1018102842941751, 1786621274035559, 253004086443112], ![2135324573170758, -341667031859563, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_1 : J0 ^ 7*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![640, 0, 0], ![-2094, -387, -292]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR71_J0_7J1_1]
 rfl
def MulR72_J0_7J1_2 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![128, 0, 0], ![-46, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![3200, 0, 0], ![-11742, -2896, -1521]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3200, 0, 0], ![256, 128, 128]], ![![-1150, 25, 0], ![-40, -55, -43]]]
 hmul := by decide
 f := ![![![![3773673539712671170272381367, -668399313433162248315429838, 207681628389356738562483337], ![283465175775261473231672650, -1825168628503060514293129650, 0]], ![![18054472884067715840, 1644119688064, 0], ![0, 0, 0]]], ![![![-13822716498749103631845035563, 2448302461862827981803181852, -760724063969566263772536873], ![-1038314183984197821826377032, 6685471927741120099097913950, 0]], ![![-66132339637896407980, -6022301637637, 0], ![0, 0, 0]]]]
 g := ![![![![1932452069731873743, -3920397917112287639, 573618124518037258], ![-3815579063195712000, 667867962369155200, 0]], ![![153717778275309526, -311849834318137998, 45628714450648712], ![-303511970938346368, 53125860643408000, 0]]], ![![![-694646522579821681, 1409241048151378030, -206194938403052557], ![1371562466874040350, -240074341231437625, 0]], ![![-23778218827392305, 48239271246970391, -7058191766713229], ![46949508005385401, -8217906568427481, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_2 : J0 ^ 7*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3200, 0, 0], ![-11742, -2896, -1521]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR72_J0_7J1_2]
 rfl

lemma PowJ0_8J1_0 : J0 ^ 8*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![256, 0, 0], ![82, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06]
 rfl     
def MulR81_J0_8J1_1 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![256, 0, 0], ![82, 1, 0]] ![![5, 0, 0], ![7, 1, 1]]
  ![![1280, 0, 0], ![3430, 705, 406]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := rfl
 M := ![![![1280, 0, 0], ![1792, 256, 256]], ![![410, 5, 0], ![626, 78, 85]]]
 hmul := by decide
 f := ![![![![55536536455761663483850, -26252851643852943621708, -5313605027387979578805], ![71437859703818144237295, -14956611522292950342390, 0]], ![![-2435775251772817152, 6191963136, 0], ![0, 0, 0]]], ![![![148601922341487313733251, -70246084293175045389145, -14217881993095132252382], ![191149898020828203698252, -40020162685118053473222, 0]], ![![-6517527161485582443, 16568149254, 0], ![0, 0, 0]]]]
 g := ![![![![13767416851981556657, -17438225800687067637, 2869842043557038043], ![28198005064450405120, -5573825238451851520, 0]], ![![19274379046299535169, -24413510362259859670, 4017777913259287807], ![39477197778279282432, -7803353493163758592, 0]]], ![![![4409875621602022985, -5585681589307947635, 919246261066699472], ![9032173315332754945, -1785365860741051910, 0]], ![![6733125918918212527, -8528380551043965279, 1403531835668499259], ![13790584014597574908, -2725948344851564491, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_1 : J0 ^ 8*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1280, 0, 0], ![3430, 705, 406]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR81_J0_8J1_1]
 rfl
def MulR82_J0_8J1_2 : IdealMulEqCertificate timesTableO ((((((((J0*J0)*J0)*J0)*J0)*J0)*J0)*J0)) (J1*J1)
  ![![256, 0, 0], ![82, 1, 0]] ![![25, 0, 0], ![2, 1, 1]]
  ![![6400, 0, 0], ![-4250, 2170, -889]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![6400, 0, 0], ![512, 256, 256]], ![![2050, 25, 0], ![216, 73, 85]]]
 hmul := by decide
 f := ![![![![37995553570480808899886064451133, -6729835442087445397060748413329, 2091060172835918687690567845961], ![2854093274868403643616077933400, -18376865865255456946958858105100, 0]], ![![-102209344754328928853760, 10232422876928, 0], ![0, 0, 0]]], ![![![-25323116143593620540802208189817, 4485272315117806555991195842741, -1393640956480393869045548694379], ![-1902184037141993135786350769228, 12247735983050613288418327071928, 0]], ![![68120052610190727281486, -6819662002349, 0], ![0, 0, 0]]]]
 g := ![![![![52707585793285, -5293306417653, -22774837305199], ![-33632325651200, 9174835385600, 0]], ![![4216605988738, -423464425698, -1821986606242], ![-2690585493248, 733986678528, 0]]], ![![![16882898492625, -1695512205195, -7295065036630], ![-10772854250100, 2938814444575, 0]], ![![1778880772227, -178649067164, -768650650974], ![-1135090829657, 309650650829, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_8J1_2 : J0 ^ 8*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6400, 0, 0], ![-4250, 2170, -889]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR82_J0_8J1_2]
 rfl
