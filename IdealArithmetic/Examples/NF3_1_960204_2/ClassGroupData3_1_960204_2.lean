import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_960204_2.RI3_1_960204_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![0, -1, 1]

def alpha1 := B.equivFun.symm ![11, -9, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![6955, -5301, -450]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![29, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![29, 0, 1]] ![![3, 0, 0], ![29, 0, 1]]
  ![![9, 0, 0], ![26, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![87, 0, 3]], ![![87, 0, 3], ![889, 3, 17]]]
 hmul := by decide
 f := ![![![![-31, 630, 8], ![-66, 144, 0]], ![![0, 0, 0], ![-18, 0, 0]]], ![![![-38, 1820, 25], ![-196, 416, 0]], ![![0, 0, 0], ![-52, 0, 0]]]]
 g := ![![![![-25, 0, -1], ![9, 0, 0]], ![![1, 0, 0], ![3, 0, 0]]], ![![![1, 0, 0], ![3, 0, 0]], ![![-18, 27, -1], ![11, 15, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![26, 0, 1]] ![![3, 0, 0], ![29, 0, 1]]
  ![![0, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![261, 0, 9]], ![![78, 0, 3], ![802, 3, 14]]]
 hmul := by decide
 f := ![![![![643089, -14504115, -817042], ![5944257, -3337230, 0]], ![![-457110, -23880, 0], ![2844, 2, 0]]]]
 g := ![![![![1812, 3, 43]], ![![18255, 30, 433]]], ![![![5481, 9, 130]], ![![55216, 91, 1310]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![0, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![0, 1, 0]]
  ![![121, 0, 0], ![-55, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![0, 11, 0]], ![![0, 11, 0], ![-1, -1, 3]]]
 hmul := by decide
 f := ![![![![0, -557, 927], ![-44, 0, 0]], ![![0, 0, 0], ![-37389, -242, 0]]], ![![![0, 257, -429], ![29, 0, 0]], ![![0, 0, 0], ![17303, 112, 0]]]]
 g := ![![![![-3696, -207032, 11091], ![0, -447337, 0]], ![![11, 336, -18], ![11, 726, 0]]], ![![![11, 336, -18], ![11, 726, 0]], ![![55, 1680, -90], ![55, 3631, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![-55, 1, 0]] ![![11, 0, 0], ![0, 1, 0]]
  ![![11, -9, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![0, 121, 0]], ![![-605, 11, 0], ![-1, -56, 3]]]
 hmul := by decide
 f := ![![![![0, 19328, -58452], ![1767, 214375, 0]], ![![-42875, 0, 0], ![-8371, -40, 0]]]]
 g := ![![![![10246, 18, 243]], ![![1125, 2, 27]]], ![![![-4555, -8, -108]], ![![-500, -1, -12]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![4245148300, 6989904, 100707453])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![-55, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![29, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![29, 0, 1]] ![![11, 0, 0], ![0, 1, 0]]
  ![![33, 0, 0], ![29, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![33, 0, 0], ![0, 3, 0]], ![![319, 0, 11], ![51, -13, 1]]]
 hmul := by decide
 f := ![![![![0, -634, 1939], ![-55, -7029, 0]], ![![-66, 0, 0], ![0, 0, 0]]], ![![![0, -557, 1704], ![-50, -6177, 0]], ![![-58, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-28, 0, -1], ![33, 0, 0]], ![![56, -33, 0], ![84, -84, 0]]], ![![![0, 0, 0], ![11, 0, 0]], ![![-329, 143, -3], ![-264, 364, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![33, 0, 0], ![29, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![29, 0, 1]] ![![121, 0, 0], ![-55, 1, 0]]
  ![![363, 0, 0], ![62, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![363, 0, 0], ![-165, 3, 0]], ![![3509, 0, 121], ![-1544, -13, -54]]]
 hmul := by decide
 f := ![![![![-60729515, -3390460003, 181632091], ![-415877, -7325822790, 0]], ![![-363, 0, 0], ![0, 0, 0]]], ![![![-10372505, -579086833, 31022561], ![-70967, -1251242460, 0]], ![![-62, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-61, 0, -1], ![363, 0, 0]], ![![-103, -39, -2], ![18, 708, 0]]], ![![![-11, 0, 0], ![121, 0, 0]], ![![408, 169, 8], ![110, -3068, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![363, 0, 0], ![62, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![26, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![9, 0, 0], ![26, 0, 1]] ![![11, 0, 0], ![0, 1, 0]]
  ![![99, 0, 0], ![62, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![99, 0, 0], ![0, 9, 0]], ![![286, 0, 11], ![51, -16, 1]]]
 hmul := by decide
 f := ![![![![0, -1420, 4348], ![-121, -15741, 0]], ![![-495, 0, 0], ![0, 0, 0]]], ![![![0, -889, 2723], ![-79, -9858, 0]], ![![-310, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-61, 0, -1], ![99, 0, 0]], ![![-57, -9, -1], ![54, 45, 0]]], ![![![-4, 0, 0], ![11, 0, 0]], ![![-9, 16, 0], ![81, -80, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![99, 0, 0], ![62, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![9, 0, 0], ![26, 0, 1]] ![![121, 0, 0], ![-55, 1, 0]]
  ![![1089, 0, 0], ![62, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1089, 0, 0], ![-495, 9, 0]], ![![3146, 0, 121], ![-1379, -16, -54]]]
 hmul := by decide
 f := ![![![![-1279193542, -71413469390, 3825726292], ![-8742250, -154304259615, 0]], ![![-7623, 0, 0], ![0, 0, 0]]], ![![![-72828251, -4065780627, 217809945], ![-497653, -8784999170, 0]], ![![-434, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-61, 0, -1], ![1089, 0, 0]], ![![-256, -99, -5], ![54, 5391, 0]]], ![![![-4, 0, 0], ![121, 0, 0]], ![![401, 176, 8], ![818, -9584, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1089, 0, 0], ![62, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
