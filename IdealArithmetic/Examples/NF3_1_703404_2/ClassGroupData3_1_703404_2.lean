import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_703404_2.RI3_1_703404_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-11, 1, 0]

def alpha1 := B.equivFun.symm ![2, 0, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![503, 83, -14]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![3, 1, 0]] ![![7, 0, 0], ![3, 1, 0]]
  ![![49, 0, 0], ![-11, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![21, 7, 0]], ![![21, 7, 0], ![9, 6, 1]]]
 hmul := by decide
 f := ![![![![8728174, 3722146, 271070], ![-20108914, -1814309, 0]], ![![0, 0, 0], ![-577857, -735, 0]]], ![![![-2018752, -860903, -62697], ![4651020, 419640, 0]], ![![0, 0, 0], ![133653, 170, 0]]]]
 g := ![![![![144, -13, 0], ![637, 0, 0]], ![![68, -6, 0], ![301, 0, 0]]], ![![![68, -6, 0], ![301, 0, 0]], ![![26, -2, 0], ![115, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![-11, 1, 0]] ![![7, 0, 0], ![3, 1, 0]]
  ![![-11, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![147, 49, 0]], ![![-77, 7, 0], ![-33, -8, 1]]]
 hmul := by decide
 f := ![![![![-4850924, -427205520, -161155406], ![-9560746, 1101047156, 0]], ![![-39784043, 189310454, 0], ![-178204, 170, 0]]]]
 g := ![![![![-55, -11, -1]], ![![-61, -22, -2]]], ![![![7, 0, 0]], ![![3, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0], ![-44, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![0, 0, 1]]]
 hmul := by decide
 f := ![![![![197, 39, 0], ![21, 0, 0]], ![![0, 0, 0], ![0, -3, 0]]], ![![![-4334, -872, 0], ![-436, 0, 0]], ![![0, 0, 0], ![1, 66, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![-21, -1, 0], ![5, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![2, 0, 0], ![-44, -4, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![-88, -8, 2], ![262, 22, -4]]]
 hmul := by decide
 f := ![![![![-65, 39, -6], ![-177, 6, 2]], ![![0, 0, 0], ![-3, 0, 0]]]]
 g := ![![![![2, 0, 0]], ![![0, 1, 0]]], ![![![-44, -4, 1]], ![![131, 11, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-27011, -9603, -995])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-44, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![7, 0, 0], ![3, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![14, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![14, 0, 0], ![0, 7, 0]], ![![6, 2, 0], ![0, 3, 1]]]
 hmul := by decide
 f := ![![![![-35, 33, 0], ![18, 36, 0]], ![![84, -126, 0], ![0, 0, 0]]], ![![![10, -12, 0], ![-5, -12, 0]], ![![-24, 42, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![2, 0, 0], ![7, 0, 0]]], ![![![1, 0, 0], ![2, 0, 0]], ![![2, 0, 0], ![7, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![14, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![7, 0, 0], ![3, 1, 0]] ![![2, 0, 0], ![-44, -4, 1]]
  ![![14, 0, 0], ![-42, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![14, 0, 0], ![-308, -28, 7]], ![![6, 2, 0], ![130, 10, -1]]]
 hmul := by decide
 f := ![![![![9, 172, 59], ![2, 0, 0]], ![![84, -420, 0], ![0, 0, 0]]], ![![![83, -496, -176], ![-1, 0, 0]], ![![-252, 1236, 0], ![0, 0, 0]]]]
 g := ![![![![182, 12, 8], ![-420, -77, 0]], ![![-3143, -184, -196], ![9527, 1694, 0]]], ![![![96, 7, 3], ![-174, -33, 0]], ![![1363, 81, 82], ![-4009, -715, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![14, 0, 0], ![-42, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![-11, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![49, 0, 0], ![-11, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![98, 0, 0], ![38, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![98, 0, 0], ![0, 49, 0]], ![![-22, 2, 0], ![0, -11, 1]]]
 hmul := by decide
 f := ![![![![-98, 7918, 0], ![3960, -1798, 0]], ![![-441, 44051, 0], ![0, 0, 0]]], ![![![-38, 3065, 0], ![1533, -696, 0]], ![![-171, 17052, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-19, 0, 0], ![49, 0, 0]]], ![![![-1, 0, 0], ![2, 0, 0]], ![![19, 0, 0], ![-49, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![98, 0, 0], ![38, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![49, 0, 0], ![-11, 1, 0]] ![![2, 0, 0], ![-44, -4, 1]]
  ![![98, 0, 0], ![-28, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![98, 0, 0], ![-2156, -196, 49]], ![![-22, 2, 0], ![746, 66, -15]]]
 hmul := by decide
 f := ![![![![-362, 3945, -354], ![-12, 0, 0]], ![![-441, 17640, 0], ![0, 0, 0]]], ![![![138, -1120, 100], ![5, 0, 0]], ![![126, -5022, 0], ![0, 0, 0]]]]
 g := ![![![![-26579, -3860, 360], ![7840, 10780, 0]], ![![603862, 87694, -8190], ![-176155, -244706, 0]]], ![![![5798, 842, -79], ![-1630, -2343, 0]], ![![-208756, -30316, 2831], ![60951, 84601, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![98, 0, 0], ![-28, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
