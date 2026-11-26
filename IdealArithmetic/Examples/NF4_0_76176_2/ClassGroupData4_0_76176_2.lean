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

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, 0, -1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0, 0], ![0, 0, -1, 1]] ![![2, 0, 0, 0], ![0, 0, -1, 1]]
  ![![2, 0, 0, 0], ![0, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0, 0], ![0, 0, -2, 2]], ![![0, 0, -2, 2], ![-16, 0, -5, 8]]]
 hmul := by decide
 f := ![![![![439251, 10541, 2010644, -2068268], ![3781373, 19298, -26064, 0]], ![![0, 0, 0, 0], ![1113, -72, -3, 0]]], ![![![406, 9, 1854, -1906], ![3489, 18, -24, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]]]]
 g := ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, -1, 1], ![0, 0, 0, 0]]], ![![![0, 0, -1, 1], ![0, 0, 0, 0]], ![![-8, 0, -2, 3], ![-1, 0, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0, 0], ![0, 0, 1, -2]] ![![2, 0, 0, 0], ![0, 0, -1, 1]]
  ![![4, 0, 0, 0], ![0, 1, 0, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0, 0], ![0, 0, -2, 2]], ![![0, 0, 2, -4], ![6, -6, -5, 10]]]
 hmul := by decide
 f := ![![![![-3147, -86, -14798, 15215], ![-27866, -140, 189, 0]], ![![0, 0, 0, 0], ![-6, 0, 0, 0]]], ![![![-15461, -404, -72604, 74626], ![-136767, -692, 927, 0]], ![![0, 0, 0, 0], ![-30, 1, 0, 0]]]]
 g := ![![![![13699, -14904, -20454, 37635], ![-13134, 9096, -6, 0]], ![![-6714, 7304, 10024, -18444], ![6439, -4458, 3, 0]]], ![![![13437, -14619, -20062, 36914], ![-12882, 8922, -6, 0]], ![![-73551, 80017, 109816, -202059], ![70523, -48837, 33, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![4, 0, 0, 0], ![0, 1, 0, -1]] ![![2, 0, 0, 0], ![0, 0, -1, 1]]
  ![![4, 0, 0, 0], ![-2, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![8, 0, 0, 0], ![0, 0, -4, 4]], ![![0, 2, 0, -2], ![-20, 1, -2, 1]]]
 hmul := by decide
 f := ![![![![22809271, 548786, 231314184, -234267639], ![450147139, 1014920, -1367002, 0]], ![![185080, -23135, 0, 0], ![-2253, 1194, -9, 0]]], ![![![-15182619, -365295, -153970584, 155936509], ![-299633227, -675564, 909923, 0]], ![![-123200, 15400, 0, 0], ![1500, -795, 6, 0]]]]
 g := ![![![![2, 0, 0, 0], ![0, 0, 0, 0]], ![![0, 0, -1, 1], ![0, 0, 0, 0]]], ![![![2, 0, 0, -1], ![0, -2, 0, 0]], ![![-3, 0, -1, 1], ![2, -1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![4, 0, 0, 0], ![-2, 0, 1, -2]] ![![2, 0, 0, 0], ![0, 0, -1, 1]]
  ![![8, 0, 0, 0], ![-6, 0, -5, 6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![8, 0, 0, 0], ![0, 0, -4, 4]], ![![-4, 0, 2, -4], ![6, -6, -3, 8]]]
 hmul := by decide
 f := ![![![![-15079, -371, -152770, 154760], ![-297304, -668, 903, 0]], ![![52, 36, 0, 0], ![-12, 0, 0, 0]]], ![![![10994, 266, 111322, -112767], ![216653, 488, -658, 0]], ![![-39, -27, 0, 0], ![9, 0, 0, 0]]]]
 g := ![![![![-10109, 4032, 4308, -10743], ![-3162, -1512, -42, 0]], ![![1688, -672, -716, 1788], ![531, 252, 7, 0]]], ![![![3374, -1344, -1432, 3576], ![1060, 504, 14, 0]], ![![8554, -3408, -3638, 9075], ![2674, 1278, 35, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![8, 0, 0, 0], ![-6, 0, -5, 6]] ![![2, 0, 0, 0], ![0, 0, -1, 1]]
  ![![-2, 0, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![16, 0, 0, 0], ![0, 0, -8, 8]], ![![-12, 0, -10, 12], ![-70, 6, -9, 16]]]
 hmul := by decide
 f := ![![![![695669099263, 17354414132, 14706601671418, -14797443870453], ![29033259828032, 30732967439, -41637433725, 0]], ![![978577695, -2837457, 0, 0], ![-159309, -2268, -14, 0]]]]
 g := ![![![![-2, 0, -2, 4]], ![![-6, 6, 6, -11]]], ![![![-6, 6, 8, -15]], ![![-1, 0, 12, -23]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![-10, 4, 3, -9]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![6, 0, 0, 0], ![-10, 4, 3, -9]] ![![6, 0, 0, 0], ![-10, 4, 3, -9]]
  ![![0, 0, -1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![36, 0, 0, 0], ![-60, 24, 18, -54]], ![![-60, 24, 18, -54], ![-92, -80, -41, 84]]]
 hmul := by decide
 f := ![![![![47850994405762375230, 9804582633862492832, 38405909423103221833, -60514761151451272693], ![36759827518366223147, -12228380779160526992, 67188903492028635, 0]], ![![0, 0, 0, 0], ![-19820174773, -2385884, 34, 0]]]]
 g := ![![![![-6, 0, 6, -12]], ![![8, -18, -22, 43]]], ![![![8, -18, -22, 43]], ![![3, 2, -14, 41]]]]
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

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![-10, 4, 3, -9]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, 0, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0, 0], ![0, 0, -1, 1]] ![![6, 0, 0, 0], ![-10, 4, 3, -9]]
  ![![6, 0, 0, 0], ![-4, 1, 0, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![12, 0, 0, 0], ![-20, 8, 6, -18]], ![![0, 0, -6, 6], ![-52, -8, -3, 6]]]
 hmul := by decide
 f := ![![![![1361905200232, 279051923060, 1093085073911, -1722333441939], ![1046235314856, -348036556404, 1912287132, 0]], ![![0, 0, 0, 0], ![-6489, -756, 9, 0]]], ![![![-909650874355, -186385826096, -730099123693, 1150389998623], ![-698806986551, 232462404718, -1277264865, 0]], ![![0, 0, 0, 0], ![4334, 505, -6, 0]]]]
 g := ![![![![-882, 10350, 16254, -27134], ![15888, -3876, -12, 0]], ![![-616, 6091, 9576, -15974], ![9422, -2298, 0, 0]]], ![![![-1078, 12274, 19278, -32179], ![18864, -4602, -12, 0]], ![![6475, -74335, -116739, 194887], ![-114140, 27855, 78, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0, 0], ![-4, 1, 0, -3]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0, 0], ![0, 0, 1, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![2, 0, 0, 0], ![0, 0, 1, -2]] ![![6, 0, 0, 0], ![-10, 4, 3, -9]]
  ![![12, 0, 0, 0], ![-6, 4, -3, 4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![12, 0, 0, 0], ![-20, 8, 6, -18]], ![![0, 0, 6, -12], ![-2, -14, -19, 34]]]
 hmul := by decide
 f := ![![![![220593019, 45199106, 177051184, -278972955], ![169462758, -56372820, 309741, 0]], ![![0, 0, 0, 0], ![-6, 0, 0, 0]]], ![![![-7574179106, -1551935589, -6079147219, 9578685906], ![-5818594332, 1935590941, -10635123, 0]], ![![0, 0, 0, 0], ![203, -4, 0, 0]]]]
 g := ![![![![2489035585, -746715571, -2000599768, 3309823309], ![110001408, 1216713660, -59760, 0]], ![![-4159851903, 1247963750, 3343543512, -5531610283], ![-183842099, -2033457728, 99875, 0]]], ![![![-8246925, 2474093, 6628593, -10966447], ![-364464, -4031340, 198, 0]], ![![-386424021, 115927964, 310594119, -513851731], ![-17077765, -188895406, 9278, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0, 0], ![-6, 4, -3, 4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0], ![0, 1, 0, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![4, 0, 0, 0], ![0, 1, 0, -1]] ![![6, 0, 0, 0], ![-10, 4, 3, -9]]
  ![![12, 0, 0, 0], ![10, -4, -5, 10]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![24, 0, 0, 0], ![-40, 16, 12, -36]], ![![0, 6, 0, -6], ![-60, -5, 6, -17]]]
 hmul := by decide
 f := ![![![![2604714057263392, 533701219013351, 2090581681689263, -3294051692982822], ![2000979097555467, -665637898941687, 3657351332106, 0]], ![![22646115, 314895, 0, 0], ![2925, 666, 27, 0]]], ![![![2829369661999320, 579732747799176, 2270893563003113, -3578162408727169], ![2173562789792916, -723048916594440, 3972796504660, 0]], ![![24599376, 342055, 0, 0], ![3176, 735, 30, 0]]]]
 g := ![![![![39786, -8490, 14676, -21950], ![11580, 29640, 12, 0]], ![![-117182, 25008, -43219, 64637], ![-34100, -87296, -36, 0]]], ![![![-19072, 4072, -7027, 10507], ![-5538, -14202, -6, 0]], ![![-83605, 17842, -30831, 46109], ![-24319, -62277, -25, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0, 0], ![10, -4, -5, 10]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0, 0], ![-2, 0, 1, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![4, 0, 0, 0], ![-2, 0, 1, -2]] ![![6, 0, 0, 0], ![-10, 4, 3, -9]]
  ![![24, 0, 0, 0], ![28, -19, -8, 25]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![24, 0, 0, 0], ![-40, 16, 12, -36]], ![![-12, 0, 6, -12], ![18, -22, -25, 52]]]
 hmul := by decide
 f := ![![![![-5711439620567, -1170263700136, -4584085144088, 7222972239819], ![-4387610697552, 1459565449842, -8019588609, 0]], ![![51072, -1188, 0, 0], ![-36, 0, 0, 0]]], ![![![388020802480020, 79504764158388, 311431182750667, -490710516256905], ![298083204399613, -99159195359360, 544830623161, 0]], ![![-3469704, 80694, 0, 0], ![2466, -19, 0, 0]]]]
 g := ![![![![-13575557635755, -27093242788, -17234081608500, 25351537129165], ![16335843287958, -5981370292248, 188934, 0]], ![![40592804740258, 81012562770, 51532300063377, -75804620639859], ![-48846442602803, 17885128763584, -564939, 0]]], ![![![6772905160344, 13516937495, 8598158793336, -12647992904033], ![-8150023761252, 2984131834974, -94260, 0]], ![![-34871041593383, -69593428275, -44268559179622, 65119572205328], ![41961287045570, -15364128520021, 485308, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0, 0], ![28, -19, -8, 25]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0, 0], ![-6, 0, -5, 6]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![8, 0, 0, 0], ![-6, 0, -5, 6]] ![![6, 0, 0, 0], ![-10, 4, 3, -9]]
  ![![24, 0, 0, 0], ![10, -10, 7, -8]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![48, 0, 0, 0], ![-80, 32, 24, -72]], ![![-36, 0, -30, 36], ![-146, -42, -11, 44]]]
 hmul := by decide
 f := ![![![![-10025896418416629943, -2054288122426761272, -8046931416806040802, 12679250131634025837], ![-7702038956777516766, 2562130222540713690, -14077640693967999, 0]], ![![-42249154860, -43903629, 0, 0], ![2209887, -14994, 147, 0]]], ![![![3813303517960678077, 781339024185924476, 3060613295797530528, -4822494379978764481], ![2929435037389731512, -974494427564698874, 5354365788607711, 0]], ![![16069271460, 16698539, 0, 0], ![-840513, 5702, -56, 0]]]]
 g := ![![![![2232007752, -1132162038, -1863780315, 3287015104], ![-237536880, -799887648, 24, 0]], ![![-6679087402, 3387895590, 5577199087, -9836104341], ![710808296, 2393593616, -72, 0]]], ![![![-1674003974, 849120596, 1397833696, -2465258613], ![178152468, 599915076, -18, 0]], ![![-2905239593, 1473651680, 2425945138, -4278464712], ![309184212, 1041154656, -31, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![24, 0, 0, 0], ![10, -10, 7, -8]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
