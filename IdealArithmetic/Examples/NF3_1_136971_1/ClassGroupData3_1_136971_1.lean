import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_136971_1.RI3_1_136971_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![58, 11, 3]

def alpha1 := B.equivFun.symm ![18, -5, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![50, -10, -1]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![-1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![1, 2, 1]]]
 hmul := by decide
 f := ![![![![0, -2, -1], ![0, 0, 0]], ![![0, 0, 0], ![4, 0, 0]]], ![![![0, 28, 8], ![0, 19, 0]], ![![0, 0, 0], ![-72, 1, 0]]]]
 g := ![![![![4, -3, 0], ![12, 0, 0]], ![![1, 1, -1], ![2, 4, 0]]], ![![![1, 1, -1], ![2, 4, 0]], ![![0, 1, 0], ![-1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![-1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![58, 11, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![-2, 2, 0], ![-1, 0, 1]]]
 hmul := by decide
 f := ![![![![0, 13, -66], ![0, -26, 0]], ![![0, -44, 0], ![723, 11, 0]]]]
 g := ![![![![-17, 1, 1]], ![![27, -11, 1]]], ![![![22, -6, 0]], ![![11, 8, -3]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![7, 0, 0], ![2, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![49, 0, 0], ![16, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![14, 7, 0]], ![![14, 7, 0], ![4, 4, 1]]]
 hmul := by decide
 f := ![![![![-73397, -40662, -1936], ![253386, 11606, 0]], ![![0, 0, 0], ![14014, -98, 0]]], ![![![-22482, -12455, -593], ![77614, 3555, 0]], ![![0, 0, 0], ![4292, -30, 0]]]]
 g := ![![![![321, 20, 0], ![-980, 0, 0]], ![![78, 5, 0], ![-238, 0, 0]]], ![![![78, 5, 0], ![-238, 0, 0]], ![![4, 0, 0], ![-12, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![49, 0, 0], ![16, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![18, -5, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![343, 0, 0], ![98, 49, 0]], ![![112, 7, 0], ![32, 18, 1]]]
 hmul := by decide
 f := ![![![![23686804, 13478005, 944805], ![-82639452, -6724598, 0]], ![![-226596, 779205, 0], ![-16420, -46, 0]]]]
 g := ![![![![-474, -90, -25]], ![![-389, -72, -20]]], ![![![-191, -36, -10]], ![![-156, -29, -8]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-3026, -571, -156])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![16, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![1, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![14, 0, 0], ![-5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![14, 0, 0], ![4, 2, 0]], ![![7, 7, 0], ![2, 3, 1]]]
 hmul := by decide
 f := ![![![![128, 66, -4], ![-420, -21, 0]], ![![-14, 14, 0], ![0, 0, 0]]], ![![![-48, -26, 1], ![158, 14, 0]], ![![5, -6, 0], ![0, 0, 0]]]]
 g := ![![![![26, -5, 0], ![70, 0, 0]], ![![16, -3, 0], ![44, 0, 0]]], ![![![13, -2, 0], ![35, 0, 0]], ![![8, -1, 0], ![22, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![14, 0, 0], ![-5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![1, 1, 0]] ![![49, 0, 0], ![16, 1, 0]]
  ![![98, 0, 0], ![-33, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![98, 0, 0], ![32, 2, 0]], ![![49, 49, 0], ![16, 17, 1]]]
 hmul := by decide
 f := ![![![![33938, 2566, -21], ![-103782, -1372, 0]], ![![-98, 98, 0], ![0, 0, 0]]], ![![![-11449, -874, 7], ![35011, 490, 0]], ![![33, -34, 0], ![0, 0, 0]]]]
 g := ![![![![166, -5, 0], ![490, 0, 0]], ![![100, -3, 0], ![296, 0, 0]]], ![![![83, -2, 0], ![245, 0, 0]], ![![50, -1, 0], ![148, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![98, 0, 0], ![-33, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![-1, 1, 0]] ![![7, 0, 0], ![2, 1, 0]]
  ![![28, 0, 0], ![-5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![28, 0, 0], ![8, 4, 0]], ![![-7, 7, 0], ![-2, 1, 1]]]
 hmul := by decide
 f := ![![![![184, 76, 29], ![-616, -56, 0]], ![![28, -84, 0], ![0, 0, 0]]], ![![![-34, -15, -6], ![114, 14, 0]], ![![-5, 16, 0], ![0, 0, 0]]]]
 g := ![![![![106, -21, 0], ![588, 0, 0]], ![![36, -7, 0], ![200, 0, 0]]], ![![![-19, 9, -1], ![-105, 28, 0]], ![![-4, 1, 0], ![-22, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![28, 0, 0], ![-5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![-1, 1, 0]] ![![49, 0, 0], ![16, 1, 0]]
  ![![196, 0, 0], ![-33, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![196, 0, 0], ![64, 4, 0]], ![![-49, 49, 0], ![-16, 15, 1]]]
 hmul := by decide
 f := ![![![![182164, 13588, 616], ![-557424, -8575, 0]], ![![588, -1764, 0], ![0, 0, 0]]], ![![![-30661, -2295, -105], ![93823, 1470, 0]], ![![-99, 300, 0], ![0, 0, 0]]]]
 g := ![![![![3928, -119, 0], ![23324, 0, 0]], ![![1288, -39, 0], ![7648, 0, 0]]], ![![![-949, 62, -1], ![-5635, 196, 0]], ![![-256, 41, -1], ![-1520, 197, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![196, 0, 0], ![-33, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
