import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_916300_1.RI3_1_916300_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![63, -10, -4]

def alpha1 := B.equivFun.symm ![-29, 7, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-5551, -2043, 1357]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![9, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![0, 0, 1]]]
 hmul := by decide
 f := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![-17, 4, 0], ![4, 0, 0]], ![![0, 0, 0], ![-1, 1, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![3, 0, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![63, -10, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![0, 9, 0]], ![![0, 3, 0], ![0, 0, 1]]]
 hmul := by decide
 f := ![![![![-60, 0, 0], ![60, -2, 2]], ![![-11, 0, 0], ![3, -7, 0]]]]
 g := ![![![![-60131, -2186, -1144]], ![![-58344, -2121, -1110]]], ![![![-19448, -707, -370]], ![![-18870, -686, -359]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![-2, 1, 0]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![11, 0, 0], ![26, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-22, 11, 0]], ![![-22, 11, 0], ![4, -4, 1]]]
 hmul := by decide
 f := ![![![![-11389663, 5867570, -86034], ![-62417466, 822471, 0]], ![![0, 0, 0], ![1354083, -2950, 0]]], ![![![-27790760, 14316858, -209921], ![-152298520, 2006808, 0]], ![![0, 0, 0], ![3303960, -7198, 0]]]]
 g := ![![![![-15, 4, -1], ![11, 0, 0]], ![![-2, 1, 0], ![0, 0, 0]]], ![![![-2, 1, 0], ![0, 0, 0]], ![![-2, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![11, 0, 0], ![26, -4, 1]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![-29, 7, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![121, 0, 0], ![-22, 11, 0]], ![![286, -44, 11], ![101, -13, -5]]]
 hmul := by decide
 f := ![![![![-32826, 16816, -218], ![-179876, 2464, 0]], ![![0, 0, 0], ![145, 0, 0]]]]
 g := ![![![![-632, -23, -12]], ![![-52, -2, -1]]], ![![![-1313, -47, -25]], ![![-109, -4, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![5018755298, 182451403, 95482308])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![26, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![33, 0, 0], ![9, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![33, 0, 0], ![-6, 3, 0]], ![![0, 11, 0], ![0, -2, 1]]]
 hmul := by decide
 f := ![![![![69, -34, 8], ![374, 0, 0]], ![![0, -24, 0], ![0, 0, 0]]], ![![![21, -10, 3], ![114, 0, 0]], ![![-1, -9, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-1, 0, 0], ![3, 0, 0]]], ![![![-3, 0, 0], ![11, 0, 0]], ![![3, 0, 0], ![-11, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![33, 0, 0], ![9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![26, -4, 1]]
  ![![33, 0, 0], ![15, 7, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![33, 0, 0], ![78, -12, 3]], ![![0, 11, 0], ![153, -21, -3]]]
 hmul := by decide
 f := ![![![![1, 10, 3], ![0, 0, 0]], ![![-30, -9, 0], ![0, 0, 0]]], ![![![-9, 6, 1], ![4, 0, 0]], ![![-13, -4, 0], ![0, 0, 0]]]]
 g := ![![![![1510, -499, 75], ![597, -384, 0]], ![![3400, -1122, 169], ![1338, -864, 0]]], ![![![122, -43, 6], ![58, -32, 0]], ![![6804, -2242, 338], ![2667, -1728, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![33, 0, 0], ![15, 7, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![9, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![-2, 1, 0]]
  ![![99, 0, 0], ![9, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![99, 0, 0], ![-18, 9, 0]], ![![0, 11, 0], ![0, -2, 1]]]
 hmul := by decide
 f := ![![![![221, -112, 9], ![1210, -11, 0]], ![![0, -72, 0], ![0, 0, 0]]], ![![![1, 0, 1], ![5, 0, 0]], ![![-4, -9, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-1, 0, 0], ![9, 0, 0]]], ![![![-1, 0, 0], ![11, 0, 0]], ![![1, 0, 0], ![-11, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![99, 0, 0], ![9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![9, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![26, -4, 1]]
  ![![99, 0, 0], ![-18, 7, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![99, 0, 0], ![234, -36, 9]], ![![0, 11, 0], ![153, -21, -3]]]
 hmul := by decide
 f := ![![![![1, 10, 3], ![0, 0, 0]], ![![-90, -27, 0], ![0, 0, 0]]], ![![![-12, 0, -1], ![5, 0, 0]], ![![17, 5, 0], ![0, 0, 0]]]]
 g := ![![![![9199, -3920, 518], ![-1890, -6174, 0]], ![![19696, -8394, 1111], ![-4140, -13230, 0]]], ![![![600, -255, 32], ![-32, -392, 0]], ![![13141, -5600, 740], ![-2703, -8820, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![99, 0, 0], ![-18, 7, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
