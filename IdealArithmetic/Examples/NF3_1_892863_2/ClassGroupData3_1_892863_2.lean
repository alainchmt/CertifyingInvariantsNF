import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_892863_2.RI3_1_892863_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-302684, 63841, 617]

def alpha1 := B.equivFun.symm ![14113447032, 623435208, 437195305]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![310563493681, -64302237730, -2097847190]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![18, 1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![18, 1, 1]] ![![2, 0, 0], ![18, 1, 1]]
  ![![4, 0, 0], ![20, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![36, 2, 2]], ![![36, 2, 2], ![536, 27, 11]]]
 hmul := by decide
 f := ![![![![1308348, -7021156, -2264671], ![7132248, -865620, 0]], ![![0, 0, 0], ![-1064, -4, 0]]], ![![![6542960, -35112301, -11325458], ![35667864, -4328904, 0]], ![![0, 0, 0], ![-5321, -20, 0]]]]
 g := ![![![![-8, -14, -5], ![32, -4, 0]], ![![58, -119, -38], ![262, -36, 0]]], ![![![58, -119, -38], ![262, -36, 0]], ![![893, -1771, -569], ![3895, -536, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![20, 1, 1]] ![![2, 0, 0], ![18, 1, 1]]
  ![![8, 0, 0], ![20, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![72, 4, 4]], ![![40, 2, 2], ![572, 29, 13]]]
 hmul := by decide
 f := ![![![![2492344008, -13391167172, -4310747139], ![13580139016, -1650274416, 0]], ![![-10409712, -1739952, 0], ![-2000, -8, 0]]], ![![![6232089026, -33484521225, -10778993512], ![33957044018, -4126499804, 0]], ![![-26029413, -4350738, 0], ![-5001, -20, 0]]]]
 g := ![![![![3808, -2208, -615], ![9168, -1416, 0]], ![![34220, -19847, -5528], ![82412, -12728, 0]]], ![![![19004, -11028, -3072], ![45794, -7072, 0]], ![![271970, -157687, -43920], ![654757, -101128, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![8, 0, 0], ![20, 1, 1]] ![![2, 0, 0], ![18, 1, 1]]
  ![![16, 0, 0], ![12, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![144, 8, 8]], ![![40, 2, 2], ![572, 29, 13]]]
 hmul := by decide
 f := ![![![![1779359586, -9561853607, -3077882310], ![9694368334, -1178667360, 0]], ![![-6899808, -1159968, 0], ![-4000, -16, 0]]], ![![![1334958367, -7173747637, -2309170571], ![7273166354, -884291115, 0]], ![![-5176557, -870262, 0], ![-3001, -12, 0]]]]
 g := ![![![![149456, -28404, -2275], ![110176, -24592, 0]], ![![1344516, -255525, -20466], ![991160, -221232, 0]]], ![![![373484, -70983, -5686], ![275346, -61456, 0]], ![![5340952, -1015038, -81297], ![3937213, -878816, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![16, 0, 0], ![12, 1, 1]] ![![2, 0, 0], ![18, 1, 1]]
  ![![32, 0, 0], ![12, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![288, 16, 16]], ![![24, 2, 2], ![428, 21, 5]]]
 hmul := by decide
 f := ![![![![2519623508394, -13540974043987, -4358072923618], ![13727088091814, -1669357499520, 0]], ![![-18906520768, -1350473664, 0], ![-10048, -32, 0]]], ![![![945108111178, -5079205031857, -1634708540976], ![5149016214210, -626174231188, 0]], ![![-7091815929, -506561242, 0], ![-3769, -12, 0]]]]
 g := ![![![![203696, -23884, 2245], ![75712, -49184, 0]], ![![1832472, -214862, 20197], ![681104, -442464, 0]]], ![![![152664, -17902, 1682], ![56770, -36864, 0]], ![![2723396, -319325, 30016], ![1012245, -657584, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![32, 0, 0], ![12, 1, 1]] ![![2, 0, 0], ![18, 1, 1]]
  ![![-302684, 63841, 617]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![576, 32, 32]], ![![24, 2, 2], ![428, 21, 5]]]
 hmul := by decide
 f := ![![![![-138886255945630639, 746423900111260073, 240243801570172838], ![-756642452669959162, 92025668444070123, 0]], ![![1025711387785335, 73265173753830, 0], ![94978935, 302684, 0]]]]
 g := ![![![![530097593941, 23416072841, 16420947961]], ![![7039630757775, 310962563275, 218068166427]]], ![![![340583623497, 15044646547, 10550332659]], ![![4522908571871, 199791053162, 140107118274]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow6 : J0 ^ 6 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![18, 2, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![2, 0, 0], ![18, 2, 1]] ![![2, 0, 0], ![18, 2, 1]]
  ![![14113447032, 623435208, 437195305]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![36, 4, 2]], ![![36, 4, 2], ![840, 12, 21]]]
 hmul := by decide
 f := ![![![![1237606591635483, -6440008708615616, -344810699615055], ![4526045266296293, -547461052021332, 0]], ![![0, 0, 0], ![-381500265169, -14113447032, 0]]]]
 g := ![![![![56237, -6292, -6909]], ![![-700650, 112804, 44096]]], ![![![-700650, 112804, 44096]], ![![6953736, -1315944, -198039]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![550070704109271125344321, 24298347742654449765430, 17039659319891780055290])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![18, 2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![18, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![18, 1, 1]] ![![2, 0, 0], ![18, 2, 1]]
  ![![2, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![36, 4, 2]], ![![36, 2, 2], ![687, 19, 14]]]
 hmul := by decide
 f := ![![![![249563, -1298607, -68979], ![913073, -110442, 0]], ![![-2007, 0, 0], ![-2, 0, 0]]], ![![![124597, -648351, -34439], ![455867, -55140, 0]], ![![-1002, 0, 0], ![-1, 0, 0]]]]
 g := ![![![![1, -1, 0], ![2, 0, 0]], ![![14, -2, 1], ![8, 0, 0]]], ![![![14, -3, 1], ![8, 0, 0]], ![![284, -50, 7], ![119, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![20, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![20, 1, 1]] ![![2, 0, 0], ![18, 2, 1]]
  ![![4, 0, 0], ![37, 3, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![72, 8, 4]], ![![40, 2, 2], ![723, 23, 16]]]
 hmul := by decide
 f := ![![![![113222431, -589328179, -31339392], ![414004025, -50139572, 0]], ![![-683410, -4344, 0], ![-4, 0, 0]]], ![![![1047307270, -5451284419, -289889309], ![3829536362, -463790936, 0]], ![![-6321541, -40182, 0], ![-37, 0, 0]]]]
 g := ![![![![37, -345, -56], ![292, -36, 0]], ![![531, -2971, -473], ![2508, -312, 0]]], ![![![290, -1687, -269], ![1424, -177, 0]], ![![5518, -30664, -4884], ![25871, -3219, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![37, 3, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![20, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![8, 0, 0], ![20, 1, 1]] ![![2, 0, 0], ![18, 2, 1]]
  ![![8, 0, 0], ![-33, 1, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![16, 0, 0], ![144, 16, 8]], ![![40, 2, 2], ![723, 23, 16]]]
 hmul := by decide
 f := ![![![![1010609959, -5260904717, -279706930], ![3694731585, -447689820, 0]], ![![-5947188, -2896, 0], ![-8, 0, 0]]], ![![![-4168767248, 21701237679, 1153791387], ![-15240771804, 1846720995, 0]], ![![24532157, 11946, 0], ![33, 0, 0]]]]
 g := ![![![![127, -95, -160], ![-472, 56, 0]], ![![1078, -838, -1419], ![-4192, 496, 0]]], ![![![330, -236, -396], ![-1168, 139, 0]], ![![5501, -4264, -7208], ![-21283, 2519, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8, 0, 0], ![-33, 1, -2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![12, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![16, 0, 0], ![12, 1, 1]] ![![2, 0, 0], ![18, 2, 1]]
  ![![16, 0, 0], ![103, 1, 6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![32, 0, 0], ![288, 32, 16]], ![![24, 2, 2], ![579, 7, 8]]]
 hmul := by decide
 f := ![![![![56596411329775, -294637475596425, -15651692172556], ![206904380285385, -25076227171520, 0]], ![![-539237219016, -2899328, 0], ![-16, 0, 0]]], ![![![364339280812045, -1896728139414435, -100757735970430], ![1331946519908875, -161428160522660, 0]], ![![-3471338481491, -18664418, 0], ![-103, 0, 0]]]]
 g := ![![![![484, -1396, -1110], ![2848, -336, 0]], ![![4552, -12360, -9815], ![25184, -2976, 0]]], ![![![298, -1035, -826], ![2120, -249, 0]], ![![9341, -25209, -20014], ![51349, -6069, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![16, 0, 0], ![103, 1, 6]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![12, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![32, 0, 0], ![12, 1, 1]] ![![2, 0, 0], ![18, 2, 1]]
  ![![32, 0, 0], ![175, 13, 10]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![64, 0, 0], ![576, 64, 32]], ![![24, 2, 2], ![579, 7, 8]]]
 hmul := by decide
 f := ![![![![-2753916732340131, 14337163554576949, 761915935938219], ![-10067129068515061, 1220240443150512, 0]], ![![25825613157744, -33265664, 0], ![-32, 0, 0]]], ![![![-15060467063082700, 78406284749305116, 4166723606158099], ![-55054557015360040, 6673183247444679, 0]], ![![141233680662383, -181921418, 0], ![-175, 0, 0]]]]
 g := ![![![![5544, -16520, -3566], ![23104, -2784, 0]], ![![48807, -143115, -30861], ![200096, -24128, 0]]], ![![![1952, -6028, -1304], ![8436, -1015, 0]], ![![50827, -148787, -32081], ![208017, -25085, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![32, 0, 0], ![175, 13, 10]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl
