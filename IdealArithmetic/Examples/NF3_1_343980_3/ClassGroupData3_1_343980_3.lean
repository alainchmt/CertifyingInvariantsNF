import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_343980_3.RI3_1_343980_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-9, 9, -1]

def alpha1 := B.equivFun.symm ![3119, 1248, 159]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![813, 807, -116]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![5, 0, 0], ![-26, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-10, 5, 0], ![4, -4, 1]]]
 hmul := by decide
 f := ![![![![-24409, 13505, -641], ![-60091, 2705, 0]], ![![0, 0, 0], ![2484, -4, 0]]], ![![![116048, -64206, 3047], ![285692, -12858, 0]], ![![0, 0, 0], ![-11808, 19, 0]]]]
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![24, 5, -1], ![5, 0, 0]]], ![![![24, 5, -1], ![5, 0, 0]], ![![6, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![5, 0, 0], ![-26, -4, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![-9, 9, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-130, -20, 5], ![206, 24, -6]]]
 hmul := by decide
 f := ![![![![-17315, 9392, -450], ![-42545, 2293, 0]], ![![0, 0, 0], ![36, 0, 0]]]]
 g := ![![![![117, 47, 6]], ![![138, 55, 7]]], ![![![100, 40, 5]], ![![114, 46, 6]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![-3, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![121, 0, 0], ![30, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-33, 11, 0]], ![![-33, 11, 0], ![9, -6, 1]]]
 hmul := by decide
 f := ![![![![-2774660, 1019371, -30820], ![-9577304, 134101, 0]], ![![0, 0, 0], ![2236685, -2904, 0]]], ![![![-680288, 249930, -7557], ![-2348152, 32885, 0]], ![![0, 0, 0], ![548390, -712, 0]]]]
 g := ![![![![1891, 63, 0], ![-7623, 0, 0]], ![![-543, -48, -1], ![2189, 121, 0]]], ![![![-543, -48, -1], ![2189, 121, 0]], ![![99, 3, 0], ![-399, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![30, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![3119, 1248, 159]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![-363, 121, 0]], ![![330, 11, 0], ![-90, 27, 1]]]
 hmul := by decide
 f := ![![![![8334720289, -5507383110, -128269953], ![29058298874, 322921143, 0]], ![![-1638918748, 11964148528, 0], ![49967035, -64872, 0]]]]
 g := ![![![![7513, 762, -219]], ![![-5115, -361, 129]]], ![![![1584, 175, -48]], ![![-1104, -87, 29]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![3539271, 1416133, 180405])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![30, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![-2, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![55, 0, 0], ![8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![55, 0, 0], ![-15, 5, 0]], ![![-22, 11, 0], ![6, -5, 1]]]
 hmul := by decide
 f := ![![![![813, -369, 45], ![2816, -11, 0]], ![![110, -220, 0], ![0, 0, 0]]], ![![![120, -53, 6], ![416, 0, 0]], ![![16, -30, 0], ![0, 0, 0]]]]
 g := ![![![![41, 5, 0], ![-275, 0, 0]], ![![-17, -10, -1], ![115, 55, 0]]], ![![![-26, -11, -1], ![176, 55, 0]], ![![-6, -1, 0], ![42, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![55, 0, 0], ![8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![5, 0, 0], ![-2, 1, 0]] ![![121, 0, 0], ![30, 1, 0]]
  ![![605, 0, 0], ![-212, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![605, 0, 0], ![150, 5, 0]], ![![-242, 121, 0], ![-60, 28, 1]]]
 hmul := by decide
 f := ![![![![4710995, 172727, 1048], ![-18999057, -68244, 0]], ![![1210, -2420, 0], ![0, 0, 0]]], ![![![-1650764, -60535, -368], ![6657396, 23958, 0]], ![![-424, 850, 0], ![0, 0, 0]]]]
 g := ![![![![116177, -548, 0], ![331540, 0, 0]], ![![29046, -137, 0], ![82890, 0, 0]]], ![![![-46386, 431, -1], ![-132374, 605, 0]], ![![-11364, 266, -1], ![-32430, 606, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![605, 0, 0], ![-212, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-26, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![5, 0, 0], ![-26, -4, 1]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![55, 0, 0], ![-1, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![55, 0, 0], ![-15, 5, 0]], ![![-286, -44, 11], ![232, 28, -7]]]
 hmul := by decide
 f := ![![![![19049, -6119, 65], ![65648, -1199, 0]], ![![220, 0, 0], ![0, 0, 0]]], ![![![-341, 112, -2], ![-1174, 31, 0]], ![![-4, 0, 0], ![0, 0, 0]]]]
 g := ![![![![3327, 886, 22], ![-22, -1188, 0]], ![![-912, -244, -7], ![59, 326, 0]]], ![![![-17249, -4597, -116], ![231, 6160, 0]], ![![14001, 3731, 94], ![-177, -5000, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![55, 0, 0], ![-1, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![5, 0, 0], ![-26, -4, 1]] ![![121, 0, 0], ![30, 1, 0]]
  ![![605, 0, 0], ![219, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![605, 0, 0], ![150, 5, 0]], ![![-3146, -484, 121], ![-626, -104, 26]]]
 hmul := by decide
 f := ![![![![124563975, 4591499, 14111], ![-502357273, -1765995, 0]], ![![2420, 0, 0], ![0, 0, 0]]], ![![![45090093, 1662048, 5108], ![-181845001, -639267, 0]], ![![876, 0, 0], ![0, 0, 0]]]]
 g := ![![![![365554, 701347, 2467], ![133705, -1626240, 0]], ![![90494, 173872, 611], ![33510, -403165, 0]]], ![![![-1900544, -3645546, -12825], ![-693814, 8453060, 0]], ![![-378192, -725378, -2552], ![-137974, 1681960, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![605, 0, 0], ![219, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
