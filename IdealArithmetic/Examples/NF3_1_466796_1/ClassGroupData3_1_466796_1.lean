import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_466796_1.RI3_1_466796_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-14, -1, 0]

def alpha1 := B.equivFun.symm ![-85, 7, 1]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-396, 23, 4]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![7, 0, 0], ![0, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![49, 0, 0], ![14, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![49, 0, 0], ![0, 7, 0]], ![![0, 7, 0], ![0, 0, 1]]]
 hmul := by decide
 f := ![![![![98, -20, 0], ![3, 0, 0]], ![![0, 0, 0], ![-7, 7, 0]]], ![![![28, -6, 0], ![3, 0, 0]], ![![0, 0, 0], ![-2, 2, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-2, 0, 0], ![7, 0, 0]]], ![![![-2, 0, 0], ![7, 0, 0]], ![![4, 0, 0], ![-14, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![49, 0, 0], ![14, 1, 0]] ![![7, 0, 0], ![0, 1, 0]]
  ![![-14, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![343, 0, 0], ![0, 49, 0]], ![![98, 7, 0], ![0, 14, 1]]]
 hmul := by decide
 f := ![![![![-392, 756, 0], ![-4747, 4, -4]], ![![0, -988, 0], ![6946, -2, 0]]]]
 g := ![![![![-73, 15, -1]], ![![97, -30, 2]]], ![![![-7, 0, 0]], ![![0, -1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![11, 0, 0], ![-3, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![121, 0, 0], ![30, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![-33, 11, 0]], ![![-33, 11, 0], ![9, -6, 1]]]
 hmul := by decide
 f := ![![![![-3057236, 1121156, -33835], ![-10552432, 148390, 0]], ![![0, 0, 0], ![2465375, 726, 0]]], ![![![-749570, 274885, -8296], ![-2587234, 36386, 0]], ![![0, 0, 0], ![604460, 178, 0]]]]
 g := ![![![![1891, 63, 0], ![-7623, 0, 0]], ![![-543, -48, -1], ![2189, 121, 0]]], ![![![-543, -48, -1], ![2189, 121, 0]], ![![99, 3, 0], ![-399, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![121, 0, 0], ![30, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![-85, 7, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![1331, 0, 0], ![-363, 121, 0]], ![![330, 11, 0], ![-90, 27, 1]]]
 hmul := by decide
 f := ![![![![-296808597, 196117988, 4567516], ![-1034797412, -11497770, 0]], ![![58364484, -426030868, 0], ![-1779405, -524, 0]]]]
 g := ![![![![216, 3, -4]], ![![188, -31, 1]]], ![![![76, -2, -1]], ![![41, -5, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-667, 185, -13])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![30, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![7, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![7, 0, 0], ![0, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![77, 0, 0], ![-14, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![77, 0, 0], ![-21, 7, 0]], ![![0, 11, 0], ![0, -3, 1]]]
 hmul := by decide
 f := ![![![![19, -6, 6], ![66, 0, 0]], ![![0, -42, 0], ![0, 0, 0]]], ![![![2, 0, -1], ![8, 0, 0]], ![![-5, 7, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![7, 0, 0]]], ![![![2, 0, 0], ![11, 0, 0]], ![![2, 0, 0], ![11, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![77, 0, 0], ![-14, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![7, 0, 0], ![0, 1, 0]] ![![121, 0, 0], ![30, 1, 0]]
  ![![847, 0, 0], ![-91, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![847, 0, 0], ![210, 7, 0]], ![![0, 121, 0], ![0, 30, 1]]]
 hmul := by decide
 f := ![![![![13831, 491, 106], ![-55781, -121, 0]], ![![0, -735, 0], ![0, 0, 0]]], ![![![-1483, -79, -12], ![5981, 121, 0]], ![![-3, 77, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![7, 0, 0]]], ![![![13, 0, 0], ![121, 0, 0]], ![![13, 0, 0], ![121, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![847, 0, 0], ![-91, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![49, 0, 0], ![14, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![49, 0, 0], ![14, 1, 0]] ![![11, 0, 0], ![-3, 1, 0]]
  ![![539, 0, 0], ![63, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![539, 0, 0], ![-147, 49, 0]], ![![154, 11, 0], ![-42, 11, 1]]]
 hmul := by decide
 f := ![![![![37843935, -12330613, 211642], ![130439034, -2327875, 0]], ![![-7943782, -833, 0], ![0, 0, 0]]], ![![![4445487, -1448463, 24861], ![15322536, -273449, 0]], ![![-933147, -98, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-6, 0, 0], ![49, 0, 0]]], ![![![-1, 0, 0], ![11, 0, 0]], ![![6, 0, 0], ![-52, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![539, 0, 0], ![63, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![49, 0, 0], ![14, 1, 0]] ![![121, 0, 0], ![30, 1, 0]]
  ![![5929, 0, 0], ![-2632, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![5929, 0, 0], ![1470, 49, 0]], ![![1694, 121, 0], ![420, 44, 1]]]
 hmul := by decide
 f := ![![![![2811182097803, 103598183243, 329700688], ![-11338318186217, -39893741261, 0]], ![![-100899722, -17003, 0], ![0, 0, 0]]], ![![![-1247660576690, -45979009762, -146327964], ![5032179387442, 17705665010, 0]], ![![44781377, 7546, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![22, 0, 0], ![49, 0, 0]]], ![![![54, 0, 0], ![121, 0, 0]], ![![1188, 0, 0], ![2676, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5929, 0, 0], ![-2632, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
