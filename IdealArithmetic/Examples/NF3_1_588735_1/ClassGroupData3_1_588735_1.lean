import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_588735_1.RI3_1_588735_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-182, -1, -6]

def alpha1 := B.equivFun.symm ![36, 0, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-33, 24, -17]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![25, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![10, 5, 0], ![6, 3, 5]]]
 hmul := by decide
 f := ![![![![-2126877, 1425046, -108234], ![-565740, 0, 216468]], ![![0, 0, 0], ![-111900, 0, -130]]], ![![![-163612, 109623, -8326], ![-43520, 0, 16652]], ![![0, 0, 0], ![-8608, 0, -10]]]]
 g := ![![![![140, -80, 0], ![11, 39, -65]], ![![53, -31, 0], ![15, 15, -25]]], ![![![53, -31, 0], ![15, 15, -25]], ![![31, -19, 0], ![18, 10, -15]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![-182, -1, -6]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![50, 25, 0]], ![![10, 5, 0], ![6, 3, 5]]]
 hmul := by decide
 f := ![![![![245147475, 89613447, 1688231], ![115981685, 0, -3376462]], ![![-3250654745, 0, 2551181], ![814288, 0, 946]]]]
 g := ![![![![-3, 3, -5]], ![![-55, 30, 0]]], ![![![-11, 6, 0]], ![![-2, -1, 6]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![5, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![5, 1, 0]] ![![11, 0, 0], ![5, 1, 0]]
  ![![121, 0, 0], ![-17, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![55, 11, 0]], ![![55, 11, 0], ![27, 9, 5]]]
 hmul := by decide
 f := ![![![![898433510, 2301182243, 2946532915], ![617577257, -6482136375, 0]], ![![0, 0, 0], ![-2552858, -4356, 0]]], ![![![-128082292, -328060659, -420063005], ![-88042912, 924104961, 0]], ![![0, 0, 0], ![363940, 621, 0]]]]
 g := ![![![![3611, -33402, 9280], ![-726, -224576, 0]], ![![1633, -15135, 4205], ![-352, -101761, 0]]], ![![![1633, -15135, 4205], ![-352, -101761, 0]], ![![811, -7415, 2060], ![-94, -49851, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![-17, 1, 0]] ![![11, 0, 0], ![5, 1, 0]]
  ![![36, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![605, 121, 0]], ![![-187, 11, 0], ![-83, -13, 5]]]
 hmul := by decide
 f := ![![![![13931679952515180, 35698235479635408, 45711250368926111], ![9577875931110132, -100564748747036820, 0]], ![![5407799229000, -22710872340, 0], ![2904660, -1296, 0]]]]
 g := ![![![![31, 5, -6]], ![![-15, 21, -1]]], ![![![-7, 1, 1]], ![![2, -3, 1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-309868, -1661, -10173])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![-17, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![2, 1, 0]] ![![11, 0, 0], ![5, 1, 0]]
  ![![55, 0, 0], ![27, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![55, 0, 0], ![25, 5, 0]], ![![22, 11, 0], ![12, 6, 5]]]
 hmul := by decide
 f := ![![![![13160971, 33692342, 43131489], ![9045212, -94889223, 0]], ![![-48510, 0, -40], ![0, 0, 0]]], ![![![6580214, 16845474, 21564852], ![4522417, -47442648, 0]], ![![-24254, 0, -20], ![0, 0, 0]]]]
 g := ![![![![1276, 22785, 4410], ![1061, -48286, -40]], ![![620, 11366, 2200], ![563, -24088, -20]]], ![![![620, 11335, 2194], ![558, -24022, -20]], ![![299, 5677, 1099], ![303, -12032, -10]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![55, 0, 0], ![27, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![5, 0, 0], ![2, 1, 0]] ![![121, 0, 0], ![-17, 1, 0]]
  ![![605, 0, 0], ![-138, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![605, 0, 0], ![-85, 5, 0]], ![![242, 121, 0], ![-32, -16, 5]]]
 hmul := by decide
 f := ![![![![30137115907, -279373297208, 77619881058], ![-6543010386, -1878401098662, 0]], ![![-21031010, 0, -1580], ![0, 0, 0]]], ![![![-6866685062, 63654679349, -17685543641], ![1490812662, 427990150885, 0]], ![![4791876, 0, 360], ![0, 0, 0]]]]
 g := ![![![![705251, -52934699, 1903780], ![-247913, -230400672, -1580]], ![![-98095, 7371118, -265100], ![35007, 32083128, 220]]], ![![![303350, -22770781, 818944], ![-106758, -99110856, -680]], ![![-40138, 3013762, -108389], ![14178, 13117536, 90]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![605, 0, 0], ![-138, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![2, 1, 0]] ![![11, 0, 0], ![5, 1, 0]]
  ![![275, 0, 0], ![27, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![275, 0, 0], ![125, 25, 0]], ![![22, 11, 0], ![12, 6, 5]]]
 hmul := by decide
 f := ![![![![-87173920452, -223342935601, -285972844935], ![-59928412522, 629141030749, 0]], ![![312144096, -1753871, -715], ![0, 0, 0]]], ![![![-8534527055, -21865786423, -27997398410], ![-5867129242, 61594352072, 0]], ![![30559624, -171708, -70], ![0, 0, 0]]]]
 g := ![![![![103, -457, 0], ![121, 4004, -715]], ![![31, -205, 0], ![208, 1792, -320]]], ![![![-16, -36, 0], ![253, 308, -55]], ![![-16, -20, 0], ![212, 169, -30]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![275, 0, 0], ![27, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![25, 0, 0], ![2, 1, 0]] ![![121, 0, 0], ![-17, 1, 0]]
  ![![3025, 0, 0], ![-1348, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3025, 0, 0], ![-425, 25, 0]], ![![242, 121, 0], ![-32, -16, 5]]]
 hmul := by decide
 f := ![![![![99133297962615, -918972947508822, 255323536724985], ![-21522636469917, -6178829274714789, 0]], ![![-346559290044, -64877481, -7865], ![0, 0, 0]]], ![![![-44178284515947, 409535939708407, -113783724347704], ![9591460962670, 2753565989268523, 0]], ![![154442505514, 28912342, 3505], ![0, 0, 0]]]]
 g := ![![![![2138, -944972, 0], ![1331, -2118831, -7865]], ![![257, 133365, 0], ![1066, 299034, 1110]]], ![![![1359, -72691, 0], ![2783, -162987, -605]], ![![466, 9612, 0], ![1081, 21553, 80]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3025, 0, 0], ![-1348, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
