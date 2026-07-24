import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_547575_2.RI3_1_547575_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-10180, 12998, -21029]

def alpha1 := B.equivFun.symm ![1088424689, 7815981, 26625656]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![111741713958570832721956057899063366445, 802417587578831739855235741814339028, 2733488560834553109458603817323188290]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![28, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![28, 0, 1]] ![![2, 0, 0], ![28, 0, 1]]
  ![![4, 0, 0], ![28, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![56, 0, 2]], ![![56, 0, 2], ![772, 12, 15]]]
 hmul := by decide
 f := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![-16, 120, 4], ![0, 18, 0]], ![![0, 0, 0], ![-1, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-16, 120, 4], ![-1, 36, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![28, 0, 1]] ![![2, 0, 0], ![28, 0, 1]]
  ![![-10180, 12998, -21029]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![112, 0, 4]], ![![56, 0, 2], ![772, 12, 15]]]
 hmul := by decide
 f := ![![![![-537150209, 46119949600, 3008041033], ![-6016082066, 7018253200, 0]], ![![61427399, 150391140, 0], ![-8170925, -12998, 0]]]]
 g := ![![![![757407523999, 5438945732, 18528128211]], ![![10557803915504, 75815622008, 258270928628]]], ![![![5278901957752, 37907811004, 129135464314]], ![![73584708354692, 528412014358, 1800070460835]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![1, 3, 2]]]
 hmul := by decide
 f := ![![![![19844, -28372, 559], ![-4264, 0, -1476]], ![![0, 0, 0], ![196, 0, -4]]], ![![![40, -58, 1], ![-8, 0, -3]], ![![0, 0, 0], ![1, 0, 0]]]]
 g := ![![![![44, -12, 11], ![-76, -20, -4]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-22, 5, -6], ![41, 12, 2]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![4, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![1088424689, 7815981, 26625656]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![2, 2, 0], ![1, 3, 2]]]
 hmul := by decide
 f := ![![![![1224483793242780, -1745540726537580, 45667996432964], ![-260528466647400, 0, -91184963326590]], ![![9570433468680, 0, -398768061195], ![52957642673, 0, -1080608708]]]]
 g := ![![![![-5480, 9123, -1022]], ![![-15004, 27334, 8612]]], ![![![-7502, 13667, 4306]], ![![47921, -78357, 15820]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-64669487523602027, 163183683288373740, 256882687623546498])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![28, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![28, 0, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![2, 0, 0], ![28, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![56, 0, 2], ![52, -13, 1]]]
 hmul := by decide
 f := ![![![![3456, -4874, 129], ![-707, 0, -255]], ![![-3, 0, 0], ![0, 0, 0]]], ![![![-17851, 25171, -666], ![3662, 0, 1317]], ![![15, 0, 0], ![1, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-27, 0, -1], ![2, 0, 0]]], ![![![0, -1, 0], ![2, 0, 0]], ![![-16, -8, -1], ![3, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![28, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![28, 0, 1]] ![![4, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![26, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![8, 0, 0], ![2, 2, 0]], ![![112, 0, 4], ![52, -13, 1]]]
 hmul := by decide
 f := ![![![![12782, -3357, 3466], ![-22366, -6334, -1182]], ![![-7, 0, 0], ![0, 0, 0]]], ![![![50226, -13180, 13621], ![-87893, -24892, -4644]], ![![-28, 0, 0], ![1, 0, 0]]]]
 g := ![![![![-12, -30, -16], ![4, 0, -4]], ![![-22, 7, 3], ![3, 0, 1]]], ![![![14, -413, -216], ![28, 0, -56]], ![![0, -291, -151], ![20, 0, -39]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![26, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![28, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![28, 0, 1]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![28, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![56, 0, 2], ![52, -13, 1]]]
 hmul := by decide
 f := ![![![![2735, -3877, 102], ![-569, 0, -203]], ![![-2, 0, 0], ![0, 0, 0]]], ![![![-349176, 494880, -13016], ![72854, 0, 25914]], ![![236, 21, 0], ![1, 0, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![-7, 20, -2], ![-4, 6, 0]]], ![![![-24, -11, 0], ![8, -3, 0]], ![![-22, -72, 5], ![23, -21, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![28, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![28, 0, 1]] ![![4, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![28, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![16, 0, 0], ![4, 4, 0]], ![![112, 0, 4], ![52, -13, 1]]]
 hmul := by decide
 f := ![![![![2178, -586, 593], ![-3811, -1084, -203]], ![![-1, 0, 0], ![0, 0, 0]]], ![![![35748, -9612, 9741], ![-62558, -17808, -3332]], ![![-15, 0, 0], ![-3, 0, 0]]]]
 g := ![![![![4, 0, 0], ![0, 0, 0]], ![![-27, 2, -1], ![4, 0, 0]]], ![![![0, 1, 0], ![4, 0, 0]], ![![-22, -2, -1], ![5, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![28, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
