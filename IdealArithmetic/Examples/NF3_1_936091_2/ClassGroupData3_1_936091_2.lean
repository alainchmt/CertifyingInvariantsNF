import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_936091_2.RI3_1_936091_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![2, -1, 1]

def alpha1 := B.equivFun.symm ![1, 0, -1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-2531195, 744128, 325805]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![-2, 2, 5]]]
 hmul := by decide
 f := ![![![![-15, 12, 40], ![8, -15, 0]], ![![0, 0, 0], ![-2, 0, 0]]], ![![![1905, -1593, -5080], ![-795, 1905, 0]], ![![0, 0, 0], ![253, 1, 0]]]]
 g := ![![![![-15, 15, 40], ![4, -32, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![0, 2, 0], ![-2, 2, 5]]]
 hmul := by decide
 f := ![![![![-2233, 1786, 5742], ![894, -2233, 0]], ![![172, 0, 0], ![-254, -1, 0]]]]
 g := ![![![![1317, 31, 39]], ![![1958, 46, 58]]], ![![![979, 23, 29]], ![![1456, 34, 43]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![9, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![-1, 4, 5]]]
 hmul := by decide
 f := ![![![![-16155, 28269, 47125], ![4041, -22212, 0]], ![![0, 0, 0], ![-18081, -36, 0]]], ![![![-899, 1571, 2620], ![227, -1235, 0]], ![![0, 0, 0], ![-1005, -2, 0]]]]
 g := ![![![![-4, 5, 10], ![9, -18, 0]], ![![0, 0, 0], ![3, 0, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![2, -3, -5], ![1, 10, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![9, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![1, 0, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![27, 0, 0], ![9, 9, 0]], ![![3, 3, 0], ![-1, 4, 5]]]
 hmul := by decide
 f := ![![![![-3590, 6282, 9972], ![898, -4936, 0]], ![![-4936, -2468, 0], ![-2009, -4, 0]]]]
 g := ![![![![1149, 27, 34]], ![![1521, 36, 45]]], ![![![507, 12, 15]], ![![671, 16, 20]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![215098343087147, 5060839176979, 6368900154600])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![6, 0, 0], ![-2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![6, 0, 0], ![2, 2, 0]], ![![0, 3, 0], ![-2, 3, 5]]]
 hmul := by decide
 f := ![![![![-44, 70, 105], ![9, -57, 0]], ![![-24, -4, 0], ![0, 0, 0]]], ![![![-3, 3, 5], ![2, -3, 0]], ![![-1, 0, 0], ![0, 0, 0]]]]
 g := ![![![![25, -12, 0], ![72, 0, 0]], ![![1, 0, 0], ![2, 0, 0]]], ![![![-11, 6, 0], ![-33, 0, 0]], ![![-15, 8, 0], ![-45, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![0, 1, 0]] ![![9, 0, 0], ![1, 1, 0]]
  ![![18, 0, 0], ![-8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![18, 0, 0], ![2, 2, 0]], ![![0, 9, 0], ![-2, 3, 5]]]
 hmul := by decide
 f := ![![![![687, -888, -1710], ![-18, 3150, 0]], ![![-288, -16, 0], ![0, 0, 0]]], ![![![-256, 329, 635], ![14, -1170, 0]], ![![107, 6, 0], ![0, 0, 0]]]]
 g := ![![![![1085, 3627, -3010], ![-270, 10836, 0]], ![![1, 0, 0], ![2, 0, 0]]], ![![![-534, -1814, 1505], ![153, -5418, 0]], ![![-308, -1036, 860], ![81, -3095, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![18, 0, 0], ![-8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![12, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![12, 0, 0], ![4, 4, 0]], ![![0, 3, 0], ![-2, 3, 5]]]
 hmul := by decide
 f := ![![![![60, -114, -135], ![-15, 87, 0]], ![![144, -8, 0], ![0, 0, 0]]], ![![![31, -59, -70], ![-8, 45, 0]], ![![75, -4, 0], ![0, 0, 0]]]]
 g := ![![![![-1367, 4208, 3500], ![-96, -8400, 0]], ![![-601, 1852, 1540], ![-44, -3696, 0]]], ![![![-113, 336, 280], ![3, -672, 0]], ![![109, -337, -280], ![9, 673, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![0, 1, 0]] ![![9, 0, 0], ![1, 1, 0]]
  ![![36, 0, 0], ![-8, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![36, 0, 0], ![4, 4, 0]], ![![0, 9, 0], ![-2, 3, 5]]]
 hmul := by decide
 f := ![![![![-3754488, 4738983, 9355835], ![109395, -16986942, 0]], ![![3514536, 65084, 0], ![0, 0, 0]]], ![![![840615, -1061040, -2094735], ![-24491, 3803310, 0]], ![![-786891, -14572, 0], ![0, 0, 0]]]]
 g := ![![![![16233, 50221, -41800], ![-2196, 300960, 0]], ![![1201, 3700, -3080], ![-140, 22176, 0]]], ![![![-1366, -4229, 3520], ![189, -25344, 0]], ![![-1366, -4229, 3520], ![189, -25343, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![36, 0, 0], ![-8, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
