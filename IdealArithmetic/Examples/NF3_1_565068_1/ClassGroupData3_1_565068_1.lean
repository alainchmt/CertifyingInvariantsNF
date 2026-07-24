import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_565068_1.RI3_1_565068_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-28, -15, 7]

def alpha1 := B.equivFun.symm ![31, 18, -5]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-21692, -12581, 3512]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![1, 1, 0]]
  ![![3, 0, 0], ![20, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![3, 3, 0], ![1, 3, 5]]]
 hmul := by decide
 f := ![![![![-2592, -2909, -445], ![7776, -950, 0]], ![![0, 0, 0], ![3603, 16, 0]]], ![![![-16848, -18906, -2886], ![50544, -6179, 0]], ![![0, 0, 0], ![23420, 104, 0]]]]
 g := ![![![![-17, 0, -1], ![3, 0, 0]], ![![-19, 1, -1], ![3, 0, 0]]], ![![![-19, 1, -1], ![3, 0, 0]], ![![7, 1, 2], ![-1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![3, 0, 0], ![20, 0, 1]] ![![3, 0, 0], ![1, 1, 0]]
  ![![-28, -15, 7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![9, 0, 0], ![3, 3, 0]], ![![60, 0, 3], ![-25, -9, 1]]]
 hmul := by decide
 f := ![![![![14, 101, -28], ![-518, 21, 0]], ![![0, 0, 0], ![-56, 0, 0]]]]
 g := ![![![![-28242, 287, -949]], ![![4821, -49, 162]]], ![![![-195432, 1986, -6567]], ![![33361, -339, 1121]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![2, 1, 0]] ![![11, 0, 0], ![2, 1, 0]]
  ![![121, 0, 0], ![-9, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![22, 11, 0]], ![![22, 11, 0], ![4, 5, 5]]]
 hmul := by decide
 f := ![![![![-1069, -1131824, -1885995], ![-103081, 4089316, 0]], ![![0, 0, 0], ![653763, 968, 0]]], ![![![81, 86522, 144175], ![7884, -312608, 0]], ![![0, 0, 0], ![-49977, -74, 0]]]]
 g := ![![![![352, -39, 0], ![4719, 0, 0]], ![![64, -7, 0], ![858, 0, 0]]], ![![![64, -7, 0], ![858, 0, 0]], ![![28, -3, 0], ![376, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![-9, 1, 0]] ![![11, 0, 0], ![2, 1, 0]]
  ![![31, 18, -5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![242, 121, 0]], ![![-99, 11, 0], ![-18, -6, 5]]]
 hmul := by decide
 f := ![![![![1841132, -120321229, -226101920], ![-10603536, 483057940, 0]], ![![-1193275, 158016222, 0], ![143193, 212, 0]]]]
 g := ![![![![-77074, 783, -2590]], ![![-3418, 35, -115]]], ![![![6696, -68, 225]], ![![297, -3, 10]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![37778913445, -383914348, 1269464757])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![-9, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![1, 1, 0]] ![![11, 0, 0], ![2, 1, 0]]
  ![![33, 0, 0], ![13, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![33, 0, 0], ![6, 3, 0]], ![![11, 11, 0], ![2, 4, 5]]]
 hmul := by decide
 f := ![![![![644, 313, -60], ![-3476, -110, 0]], ![![-33, 66, 0], ![0, 0, 0]]], ![![![252, 124, -20], ![-1360, -44, 0]], ![![-13, 24, 0], ![0, 0, 0]]]]
 g := ![![![![131, 10, 0], ![-330, 0, 0]], ![![12, 1, 0], ![-30, 0, 0]]], ![![![35, 3, 0], ![-88, 0, 0]], ![![4, 0, 0], ![-10, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![33, 0, 0], ![13, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![1, 1, 0]] ![![121, 0, 0], ![-9, 1, 0]]
  ![![363, 0, 0], ![112, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![363, 0, 0], ![-27, 3, 0]], ![![121, 121, 0], ![-9, -7, 5]]]
 hmul := by decide
 f := ![![![![137052, -15225, -590], ![1839321, -363, 0]], ![![-726, 363, 0], ![0, 0, 0]]], ![![![42282, -4697, -180], ![567450, -121, 0]], ![![-224, 111, 0], ![0, 0, 0]]]]
 g := ![![![![6273, 56, 0], ![-20328, 0, 0]], ![![-561, -118, -5], ![1818, 363, 0]]], ![![![2091, 19, 0], ![-6776, 0, 0]], ![![-187, -2, 0], ![606, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![363, 0, 0], ![112, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![20, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![3, 0, 0], ![20, 0, 1]] ![![11, 0, 0], ![2, 1, 0]]
  ![![33, 0, 0], ![23, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![33, 0, 0], ![6, 3, 0]], ![![220, 0, 11], ![-5, -9, 2]]]
 hmul := by decide
 f := ![![![![-77, 31493, 52942], ![2849, -116424, 0]], ![![-66, 0, 0], ![0, 0, 0]]], ![![![-55, 21949, 36899], ![1993, -81144, 0]], ![![-46, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-22, 0, -1], ![33, 0, 0]], ![![-38, -5, 0], ![0, -28, 0]]], ![![![-1, 0, 0], ![11, 0, 0]], ![![67, 15, -2], ![68, 84, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![33, 0, 0], ![23, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![3, 0, 0], ![20, 0, 1]] ![![121, 0, 0], ![-9, 1, 0]]
  ![![363, 0, 0], ![155, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![363, 0, 0], ![-27, 3, 0]], ![![2420, 0, 121], ![-225, -9, -9]]]
 hmul := by decide
 f := ![![![![1365282, -151709, 296], ![18322909, -4235, 0]], ![![-363, 0, 0], ![0, 0, 0]]], ![![![582978, -64781, 127], ![7823917, -1823, 0]], ![![-155, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-154, 0, -1], ![363, 0, 0]], ![![-149, -17, -1], ![363, 49, 0]]], ![![![-45, 0, 0], ![121, 0, 0]], ![![-170, 51, -1], ![354, -147, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![363, 0, 0], ![155, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
