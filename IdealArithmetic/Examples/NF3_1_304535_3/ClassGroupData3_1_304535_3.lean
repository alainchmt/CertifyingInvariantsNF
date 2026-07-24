import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_304535_3.RI3_1_304535_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![47, 4, 3]

def alpha1 := B.equivFun.symm ![-48, -4, -3]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![256, -93, 41]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![9, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![1, -2, 5]]]
 hmul := by decide
 f := ![![![![0, 1223, -1220], ![0, -2433, 0]], ![![0, 0, 0], ![9459, -18, 0]]], ![![![0, 137, -140], ![0, -268, 0]], ![![0, 0, 0], ![1052, -2, 0]]]]
 g := ![![![![7, 3, 0], ![-27, 0, 0]], ![![-5, -4, -5], ![21, 9, 0]]], ![![![-5, -4, -5], ![21, 9, 0]], ![![-1, -1, 0], ![5, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![2, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![47, 4, 3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 9, 0]], ![![6, 3, 0], ![-2, 1, 5]]]
 hmul := by decide
 f := ![![![![164354, -328786, -160296], ![267077, -212345, 0]], ![![-361576, 955728, 0], ![-90394, -86, 0]]]]
 g := ![![![![-24, 1, 2]], ![![78, -13, 1]]], ![![![18, -4, 1]], ![![29, 5, -7]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![9, 0, 0], ![3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![0, 0, 5]]]
 hmul := by decide
 f := ![![![![1, -252, 0], ![756, 0, 40]], ![![0, 0, 0], ![0, -24, 0]]], ![![![-23, -84, 0], ![257, 0, 14]], ![![0, 0, 0], ![0, -8, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-1, 0, 0], ![3, 0, 0]]], ![![![-1, 0, 0], ![3, 0, 0]], ![![-2, -4, -5], ![6, 10, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![9, 0, 0], ![3, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![-48, -4, -3]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![27, 0, 0], ![0, 9, 0]], ![![9, 3, 0], ![0, 3, 5]]]
 hmul := by decide
 f := ![![![![0, -9350, -2754], ![12469, -4580, 0]], ![![-7472, 15581, 0], ![8964, 128, 0]]]]
 g := ![![![![-29, 3, 1]], ![![35, -12, 5]]], ![![![2, -3, 2]], ![![70, -4, -5]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![704041, 59109, 44516])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![3, 0, 0], ![6, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![-3, 3, 0], ![0, -1, 5]]]
 hmul := by decide
 f := ![![![![0, 0, 0], ![1, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]], ![![![0, 0, -1], ![2, 1, 0]], ![![-2, 0, 0], ![-1, 0, 0]]]]
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![-6, 0, -1], ![3, 0, 0]]], ![![![-1, 1, 0], ![0, 0, 0]], ![![2, 0, 2], ![-1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![6, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![-1, 1, 0]] ![![9, 0, 0], ![3, 1, 0]]
  ![![9, 0, 0], ![-21, -1, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![27, 0, 0], ![9, 3, 0]], ![![-9, 9, 0], ![-3, 2, 5]]]
 hmul := by decide
 f := ![![![![-6, 2, -5], ![2, 10, 0]], ![![-16, 0, 0], ![-3, 0, 0]]], ![![![11, -6, 13], ![7, -26, 0]], ![![40, 0, 0], ![7, 0, 0]]]]
 g := ![![![![612, -187, -484], ![-1179, 72, 0]], ![![288, -82, -212], ![-517, 32, 0]]], ![![![20, 2, 4], ![9, 0, 0]], ![![-131, 42, 109], ![264, -16, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-21, -1, -4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![9, 0, 0], ![2, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![9, 0, 0], ![18, -2, 4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![0, 9, 0]], ![![6, 3, 0], ![0, 2, 5]]]
 hmul := by decide
 f := ![![![![-15, 4, 5], ![-3, 13, 0]], ![![69, -48, 0], ![0, 0, 0]]], ![![![-30, 4, 12], ![-4, 20, 0]], ![![138, -80, 0], ![-4, 0, 0]]]]
 g := ![![![![99, 26, -82], ![162, -9, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![14, 7, -20], ![40, -2, 0]], ![![-16, 2, -3], ![8, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![18, -2, 4]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![9, 0, 0], ![2, 1, 0]] ![![9, 0, 0], ![3, 1, 0]]
  ![![9, 0, 0], ![3, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![81, 0, 0], ![27, 9, 0]], ![![18, 9, 0], ![6, 5, 5]]]
 hmul := by decide
 f := ![![![![17, 59, 80], ![14, -160, 0]], ![![-145, 0, 0], ![144, 0, 0]]], ![![![5, 19, 26], ![6, -52, 0]], ![![-47, 0, 0], ![47, 0, 0]]]]
 g := ![![![![9, 0, 0], ![0, 0, 0]], ![![0, 0, -1], ![9, 0, 0]]], ![![![-1, 0, -1], ![9, 0, 0]], ![![-1, 0, 0], ![5, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![3, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
