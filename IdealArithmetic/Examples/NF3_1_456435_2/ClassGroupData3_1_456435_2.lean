import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_456435_2.RI3_1_456435_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-590, -127, -56]

def alpha1 := B.equivFun.symm ![-116, -25, -11]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-32600, -719, 1913]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![2, 3, 8]]]
 hmul := by decide
 f := ![![![![-5844, 13443, -25249], ![-46024, 5966, 0]], ![![0, 0, 0], ![620, 0, 4]]], ![![![-3028, 6786, -12737], ![-23243, 3012, 1]], ![![0, 0, 0], ![309, 0, 2]]]]
 g := ![![![![15234, 175, -123], ![7664, 0, -492]], ![![-124, -1, 1], ![-62, 0, 4]]], ![![![-124, -1, 1], ![-62, 0, 4]], ![![7431, 86, -58], ![3739, 0, -240]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![-590, -127, -56]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![4, 2, 0], ![2, 5, 8]]]
 hmul := by decide
 f := ![![![![7269345711, 637239145, -140502376], ![318619573, 0, -93711639]], ![![4179192, 0, -226179], ![-111383, 0, -590]]]]
 g := ![![![![197, -1, -8]], ![![-621, 29, 8]]], ![![![-212, 14, 0]], ![![14, -85, 56]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![25, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![5, 5, 0]], ![![5, 5, 0], ![3, 5, 8]]]
 hmul := by decide
 f := ![![![![200, 425, 904], ![125, -575, 0]], ![![0, 0, 0], ![50, 0, 0]]], ![![![9754, 20734, 44096], ![6099, -28060, 0]], ![![0, 0, 0], ![2502, -1, 0]]]]
 g := ![![![![26, 51, 104], ![25, -325, 0]], ![![0, 0, 0], ![5, 0, 0]]], ![![![0, 0, 0], ![5, 0, 0]], ![![-2, -4, -8], ![1, 26, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![25, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![-116, -25, -11]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![125, 0, 0], ![25, 25, 0]], ![![5, 5, 0], ![3, 5, 8]]]
 hmul := by decide
 f := ![![![![12042657, 25533288, 53961641], ![7515189, -33864237, 0]], ![![-1375820, 703593, 0], ![-62732, 25, 0]]]]
 g := ![![![![356, 2, -17]], ![![-455, 15, 10]]], ![![![-91, 3, 2]], ![![45, -9, 4]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![132113842, 28436774, 12539497])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![10, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![2, 2, 0]], ![![0, 5, 0], ![2, 4, 8]]]
 hmul := by decide
 f := ![![![![4511, 8501, 17009], ![2605, -10640, 0]], ![![-850, 0, -10], ![0, 0, 0]]], ![![![-1814, -3419, -6842], ![-1042, 4280, 0]], ![![339, 0, 4], ![0, 0, 0]]]]
 g := ![![![![-332, 278, -2231], ![170, 2780, -10]], ![![-64, 55, -443], ![38, 552, -2]]], ![![![0, 0, 8], ![-5, -10, 0]], ![![-64, 55, -439], ![36, 548, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![0, 1, 0]] ![![25, 0, 0], ![1, 1, 0]]
  ![![50, 0, 0], ![-24, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![50, 0, 0], ![2, 2, 0]], ![![0, 25, 0], ![2, 4, 8]]]
 hmul := by decide
 f := ![![![![-538764, -1076814, -2180971], ![-64600, 6815300, 0]], ![![-21250, 0, -50], ![0, 0, 0]]], ![![![258566, 516791, 1046708], ![31038, -3270850, 0]], ![![10199, 0, 24], ![0, 0, 0]]]]
 g := ![![![![-2292, 35008, -13371], ![1850, 83400, -50]], ![![-84, 1390, -531], ![88, 3312, -2]]], ![![![24, -126, 48], ![25, -300, 0]], ![![-84, 1380, -527], ![86, 3288, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![-24, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![1, 1, 0]]
  ![![20, 0, 0], ![6, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![20, 0, 0], ![4, 4, 0]], ![![10, 5, 0], ![4, 6, 8]]]
 hmul := by decide
 f := ![![![![1953146875, 3970682535, 8300715109], ![1184765885, -5187948840, 0]], ![![-228900180, 0, -12140], ![0, 0, 0]]], ![![![585622316, 1190550661, 2488847138], ![355234599, -1555530030, 0]], ![![-68632347, 0, -3640], ![0, 0, 0]]]]
 g := ![![![![72786, 291151, 258929], ![36400, -646400, -2460]], ![![14316, 57282, 50943], ![7176, -127176, -484]]], ![![![36096, 144391, 128411], ![18055, -320570, -1220]], ![![14202, 56809, 50522], ![7102, -126124, -480]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![6, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![2, 1, 0]] ![![25, 0, 0], ![1, 1, 0]]
  ![![100, 0, 0], ![26, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![100, 0, 0], ![4, 4, 0]], ![![50, 25, 0], ![4, 6, 8]]]
 hmul := by decide
 f := ![![![![5941061855708, 11809925359008, 23609599389029], ![710039488600, -73779998327200, 0]], ![![-134103678900, 0, -302700], ![0, 0, 0]]], ![![![1544636828823, 3070502563048, 6138339848293], ![184605575694, -19182312087400, 0]], ![![-34866070467, 0, -78700], ![0, 0, 0]]]]
 g := ![![![![247950, 3702925, 1024029], ![101600, -12765000, -12300]], ![![9752, 145708, 40295], ![4016, -502296, -484]]], ![![![122957, 1836407, 507851], ![50425, -6330600, -6100]], ![![9656, 144503, 39962], ![4042, -498144, -480]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100, 0, 0], ![26, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
