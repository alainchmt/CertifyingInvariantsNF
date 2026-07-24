import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_732108_1.RI3_1_732108_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-2, 2, -1]

def alpha1 := B.equivFun.symm ![-1, 1, -1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-459031, 408505, 31091]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![3, 0, 0], ![23, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![-2, 2, 5]]]
 hmul := by decide
 f := ![![![![1825, -1639, -4460], ![-545, 2920, 0]], ![![0, 0, 0], ![-730, -2, 0]]], ![![![13690, -12292, -33456], ![-4096, 21904, 0]], ![![0, 0, 0], ![-5476, -15, 0]]]]
 g := ![![![![-20, -1, -1], ![3, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-16, 0, 1], ![2, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![3, 0, 0], ![23, 1, 1]] ![![3, 0, 0], ![0, 1, 0]]
  ![![-2, 2, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![69, 3, 3], ![35, -8, 4]]]
 hmul := by decide
 f := ![![![![120, -114, -321], ![-36, 192, 0]], ![![0, 0, 0], ![2, 0, 0]]]]
 g := ![![![![620, 8, 19]], ![![229, 3, 7]]], ![![![5024, 65, 154]], ![![1856, 24, 57]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![25, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![10, 5, 0], ![2, 6, 5]]]
 hmul := by decide
 f := ![![![![66206, -77497, -6492], ![10985, 0, -9900]], ![![0, 0, 0], ![39900, 0, -75]]], ![![![4413, -5167, -433], ![734, 0, -660]], ![![0, 0, 0], ![2661, 0, -5]]]]
 g := ![![![![15038, -29956, -37317], ![25, 186600, -75]], ![![5019, -9998, -12455], ![10, 62280, -25]]], ![![![5019, -9998, -12455], ![10, 62280, -25]], ![![6, -16, -19], ![22, 96, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![25, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![-1, 1, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![125, 0, 0], ![50, 25, 0]], ![![10, 5, 0], ![2, 6, 5]]]
 hmul := by decide
 f := ![![![![2890860, -2855793, 83611], ![585188, 0, -417709]], ![![-433021, 0, 528], ![-2127, 0, 4]]]]
 g := ![![![![-1302, -17, -40]], ![![-810, -10, -25]]], ![![![-162, -2, -5]], ![![-101, -1, -3]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![27484102963446, 355225068659, 842450380354])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![0, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![15, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![15, 0, 0], ![6, 3, 0]], ![![0, 5, 0], ![-2, 4, 5]]]
 hmul := by decide
 f := ![![![![6296, -6407, 133], ![1240, 0, -915]], ![![300, 30, 0], ![0, 0, 0]]], ![![![-1274, 1295, -27], ![-248, 0, 185]], ![![-61, -6, 0], ![0, 0, 0]]]]
 g := ![![![![-327, -326, 1108], ![45, -3360, -45]], ![![-108, -109, 370], ![21, -1122, -15]]], ![![![37, 36, -122], ![0, 370, 5]], ![![74, 72, -245], ![-2, 744, 10]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![15, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![0, 1, 0]] ![![25, 0, 0], ![2, 1, 0]]
  ![![75, 0, 0], ![27, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![75, 0, 0], ![6, 3, 0]], ![![0, 25, 0], ![-2, 4, 5]]]
 hmul := by decide
 f := ![![![![41319344, -82531178, -103046492], ![4325, 515245350, -67575]], ![![7500, 75, 0], ![0, 0, 0]]], ![![![14864573, -29690469, -37070823], ![1554, 185358752, -24310]], ![![2698, 27, 0], ![0, 0, 0]]]]
 g := ![![![![-208506, 3194422, 550783], ![-32400, -8260575, -225]], ![![-13941, 213362, 36788], ![-2124, -551742, -15]]], ![![![22937, -351594, -60622], ![3600, 909200, 25]], ![![9220, -141440, -24387], ![1468, 365754, 10]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![75, 0, 0], ![27, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![23, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![3, 0, 0], ![23, 1, 1]] ![![5, 0, 0], ![2, 1, 0]]
  ![![15, 0, 0], ![20, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![15, 0, 0], ![6, 3, 0]], ![![115, 5, 5], ![81, -6, 6]]]
 hmul := by decide
 f := ![![![![23602, -23479, 693], ![4750, 0, -3415]], ![![-30, 0, 0], ![0, 0, 0]]], ![![![31469, -31302, 924], ![6328, 0, -4553]], ![![-40, 0, 0], ![0, 0, 0]]]]
 g := ![![![![25, -60, -42], ![45, 0, -45]], ![![6, -24, -17], ![21, 0, -18]]], ![![![245, -457, -319], ![305, 0, -345]], ![![163, -323, -225], ![222, 0, -243]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![15, 0, 0], ![20, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![3, 0, 0], ![23, 1, 1]] ![![25, 0, 0], ![2, 1, 0]]
  ![![75, 0, 0], ![5, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![75, 0, 0], ![6, 3, 0]], ![![575, 25, 25], ![81, -6, 6]]]
 hmul := by decide
 f := ![![![![26194389, -52318343, -65325842], ![2825, 326637850, -42575]], ![![-75, 0, 0], ![0, 0, 0]]], ![![![1746088, -3487483, -4354548], ![199, 21773316, -2838]], ![![-5, 0, 0], ![0, 0, 0]]]]
 g := ![![![![12120, -9046, 1287], ![775, -25900, -225]], ![![962, -719, 102], ![78, -2058, -18]]], ![![![92900, -69305, 9868], ![5425, -198450, -1725]], ![![13105, -9779, 1392], ![802, -28000, -243]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![75, 0, 0], ![5, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
