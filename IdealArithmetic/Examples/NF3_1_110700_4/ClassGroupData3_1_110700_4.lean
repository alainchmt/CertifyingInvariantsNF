import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_110700_4.RI3_1_110700_4

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![27, 0, 1]

def alpha1 := B.equivFun.symm ![3, -3, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![1, -3, 0]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![-1, 1, 0]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![49, 0, 0], ![13, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![-7, 7, 0]], ![![-7, 7, 0], ![1, -2, 1]]]
 hmul := by decide
 f := ![![![![0, -133, -181], ![0, 0, 0]], ![![0, 0, 0], ![7399, -735, 0]]], ![![![0, -34, -48], ![0, 5, 0]], ![![0, 0, 0], ![1933, -192, 0]]]]
 g := ![![![![287, 22, 0], ![-1078, 0, 0]], ![![-41, -16, -1], ![154, 49, 0]]], ![![![-41, -16, -1], ![154, 49, 0]], ![![-9, -1, 0], ![34, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![13, 1, 0]] ![![7, 0, 0], ![-1, 1, 0]]
  ![![27, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![-49, 49, 0]], ![![91, 7, 0], ![-13, 12, 1]]]
 hmul := by decide
 f := ![![![![5118, -18074, -1425], ![19518, 1648, 0]], ![![-8154, 58401, 0], ![4077, -405, 0]]]]
 g := ![![![![9, 10, 3]], ![![3, -13, 1]]], ![![![3, 1, 1]], ![![1, -4, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![13, 0, 0], ![2, 1, 0]] ![![13, 0, 0], ![2, 1, 0]]
  ![![169, 0, 0], ![-24, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![169, 0, 0], ![26, 13, 0]], ![![26, 13, 0], ![4, 4, 1]]]
 hmul := by decide
 f := ![![![![-1003127, -516863, -7474], ![6497257, 85800, 0]], ![![0, 0, 0], ![153790, -1521, 0]]], ![![![148326, 76425, 1105], ![-960708, -12685, 0]], ![![0, 0, 0], ![-22740, 225, 0]]]]
 g := ![![![![3937, -164, 0], ![27716, 0, 0]], ![![650, -27, 0], ![4576, 0, 0]]], ![![![650, -27, 0], ![4576, 0, 0]], ![![100, -4, 0], ![704, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![169, 0, 0], ![-24, 1, 0]] ![![13, 0, 0], ![2, 1, 0]]
  ![![3, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![2197, 0, 0], ![338, 169, 0]], ![![-312, 13, 0], ![-48, -22, 1]]]
 hmul := by decide
 f := ![![![![1401710641, 721052555, 11876791], ![-9108095471, -152746104, 0]], ![![3274833, -21478836, 0], ![5430, -54, 0]]]]
 g := ![![![![1029, 19, 36]], ![![186, -1, 7]]], ![![![-144, -3, -5]], ![![-26, 0, -1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![271, 3, 9])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![-24, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![7, 0, 0], ![-1, 1, 0]] ![![13, 0, 0], ![2, 1, 0]]
  ![![91, 0, 0], ![41, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![91, 0, 0], ![14, 7, 0]], ![![-13, 13, 0], ![-2, 1, 1]]]
 hmul := by decide
 f := ![![![![1654, 757, 92], ![-10660, -182, 0]], ![![91, -546, 0], ![0, 0, 0]]], ![![![746, 341, 41], ![-4808, -78, 0]], ![![41, -245, 0], ![0, 0, 0]]]]
 g := ![![![![657, 16, 0], ![-1456, 0, 0]], ![![38, 1, 0], ![-84, 0, 0]]], ![![![-129, -44, -1], ![286, 91, 0]], ![![-64, -2, 0], ![142, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![91, 0, 0], ![41, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![7, 0, 0], ![-1, 1, 0]] ![![169, 0, 0], ![-24, 1, 0]]
  ![![1183, 0, 0], ![314, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1183, 0, 0], ![-168, 7, 0]], ![![-169, 169, 0], ![24, -25, 1]]]
 hmul := by decide
 f := ![![![![29308711, -1251700, 7061], ![206375026, -165113, 0]], ![![7098, -42588, 0], ![0, 0, 0]]], ![![![7779290, -332225, 1873], ![54777270, -43771, 0]], ![![1884, -11298, 0], ![0, 0, 0]]]]
 g := ![![![![183063, 583, 0], ![-689689, 0, 0]], ![![-26064, -397, -1], ![98196, 1183, 0]]], ![![![-26421, -398, -1], ![99541, 1183, 0]], ![![3544, 11, 0], ![-13352, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1183, 0, 0], ![314, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![13, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![49, 0, 0], ![13, 1, 0]] ![![13, 0, 0], ![2, 1, 0]]
  ![![637, 0, 0], ![-232, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![637, 0, 0], ![98, 49, 0]], ![![169, 13, 0], ![26, 15, 1]]]
 hmul := by decide
 f := ![![![![259607, 65233, 17050], ![-1665469, -336570, 0]], ![![-12740, 433160, 0], ![0, 0, 0]]], ![![![-94400, -23679, -6210], ![605596, 122590, 0]], ![![4640, -157780, 0], ![0, 0, 0]]]]
 g := ![![![![55681, -240, 0], ![152880, 0, 0]], ![![8602, -37, 0], ![23618, 0, 0]]], ![![![15085, -65, 0], ![41418, 0, 0]], ![![2642, -11, 0], ![7254, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![637, 0, 0], ![-232, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![49, 0, 0], ![13, 1, 0]] ![![169, 0, 0], ![-24, 1, 0]]
  ![![8281, 0, 0], ![-869, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![8281, 0, 0], ![-1176, 49, 0]], ![![2197, 169, 0], ![-312, -11, 1]]]
 hmul := by decide
 f := ![![![![20024623352, -852948845, 394119], ![141006057530, -108362293, 0]], ![![-356083, 12106822, 0], ![0, 0, 0]]], ![![![-2101367992, 89507789, -41358], ![-14797063134, 11371503, 0]], ![![37367, -1270521, 0], ![0, 0, 0]]]]
 g := ![![![![170325, -196, 0], ![1623076, 0, 0]], ![![-23458, 896, -1], ![-223538, 8281, 0]]], ![![![46075, -53, 0], ![439062, 0, 0]], ![![-5124, 6, 0], ![-48828, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![8281, 0, 0], ![-869, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
