import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_662796_4.RI3_1_662796_4

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![279, 87, 7]

def alpha1 := B.equivFun.symm ![13, 3, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![1293, 119, -18]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-6, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![13, 0, 0], ![-6, 1, 0]] ![![13, 0, 0], ![-6, 1, 0]]
  ![![169, 0, 0], ![-71, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![169, 0, 0], ![-78, 13, 0]], ![![-78, 13, 0], ![36, -12, 1]]]
 hmul := by decide
 f := ![![![![1462930463, -281451927, 6271911], ![3166899099, -81073590, 0]], ![![0, 0, 0], ![-6012513, -1352, 0]]], ![![![-616767461, 118659362, -2644221], ![-1335155953, 34180410, 0]], ![![0, 0, 0], ![2534859, 570, 0]]]]
 g := ![![![![5397, -76, 0], ![12844, 0, 0]], ![![-2338, 104, -1], ![-5564, 169, 0]]], ![![![-2338, 104, -1], ![-5564, 169, 0]], ![![1232, -17, 0], ![2932, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![169, 0, 0], ![-71, 1, 0]] ![![13, 0, 0], ![-6, 1, 0]]
  ![![279, 87, 7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![2197, 0, 0], ![-1014, 169, 0]], ![![-923, 13, 0], ![426, -77, 1]]]
 hmul := by decide
 f := ![![![![4157335860753, -790675208737, 16220199161], ![9007011041449, -210761902945, 0]], ![![599989290, -1308228084, 0], ![-9152379, -2058, 0]]]]
 g := ![![![![-3783, -67, 30]], ![![2886, 3, -19]]], ![![![1677, 26, -13]], ![![-1268, 3, 8]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![13, 0, 0], ![0, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![13, 0, 0], ![0, 1, 0]] ![![13, 0, 0], ![0, 1, 0]]
  ![![169, 0, 0], ![-52, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![169, 0, 0], ![0, 13, 0]], ![![0, 13, 0], ![0, 0, 1]]]
 hmul := by decide
 f := ![![![![39, 8, 0], ![10, 0, 0]], ![![0, 0, 0], ![0, -13, 0]]], ![![![-12, -3, 0], ![4, 0, 0]], ![![0, 0, 0], ![0, 4, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![4, 0, 0], ![13, 0, 0]]], ![![![4, 0, 0], ![13, 0, 0]], ![![16, 0, 0], ![52, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![169, 0, 0], ![-52, 1, 0]] ![![13, 0, 0], ![0, 1, 0]]
  ![![13, 3, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![2197, 0, 0], ![0, 169, 0]], ![![-676, 13, 0], ![0, -52, 1]]]
 hmul := by decide
 f := ![![![![79, 148, 0], ![-1712, 0, -2]], ![![9, -4, 0], ![0, -1, 0]]]]
 g := ![![![![-857, -39, 9]], ![![342, 13, -3]]], ![![![290, 13, -3]], ![![-114, -4, 1]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![19875, 6189, 499])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![-52, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-6, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![13, 0, 0], ![-6, 1, 0]] ![![13, 0, 0], ![0, 1, 0]]
  ![![13, 0, 0], ![-78, -6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![169, 0, 0], ![0, 13, 0]], ![![-78, 13, 0], ![0, -6, 1]]]
 hmul := by decide
 f := ![![![![-77, 12, 0], ![11, 0, 0]], ![![-167, 0, 0], ![0, 0, 0]]], ![![![462, -75, 0], ![3, -5, 0]], ![![1002, 0, 0], ![66, 0, 0]]]]
 g := ![![![![13, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![72, 7, -1], ![13, 0, 0]], ![![6, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![13, 0, 0], ![-78, -6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![13, 0, 0], ![-6, 1, 0]] ![![169, 0, 0], ![-52, 1, 0]]
  ![![169, 0, 0], ![-26, -6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![2197, 0, 0], ![-676, 13, 0]], ![![-1014, 169, 0], ![312, -58, 1]]]
 hmul := by decide
 f := ![![![![44947, -8075, 0], ![-13848, 163, 0]], ![![105965, 0, 0], ![-2119, 0, 0]]], ![![![-6906, 1242, 0], ![2156, -25, 0]], ![![-16300, 0, 0], ![326, 0, 0]]]]
 g := ![![![![474435, 83898, -5455], ![-75881, -166296, 0]], ![![-145026, -25645, 1667], ![23317, 50840, 0]]], ![![![-206784, -36565, 2377], ![33215, 72488, 0]], ![![63184, 11174, -727], ![-9976, -22140, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![-26, -6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![-71, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![169, 0, 0], ![-71, 1, 0]] ![![13, 0, 0], ![0, 1, 0]]
  ![![169, 0, 0], ![-52, -6, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![2197, 0, 0], ![0, 169, 0]], ![![-923, 13, 0], ![0, -71, 1]]]
 hmul := by decide
 f := ![![![![-273, -18, 0], ![0, 4, 0]], ![![-650, -52, 0], ![0, 0, 0]]], ![![![84, -51, 0], ![9, 9, 0]], ![![200, -116, 0], ![-12, 0, 0]]]]
 g := ![![![![28873, 3650, -331], ![-8957, -10816, 0]], ![![-3588, -453, 41], ![1183, 1352, 0]]], ![![![-12395, -1567, 142], ![3890, 4648, 0]], ![![1548, 195, -18], ![-365, -568, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![-52, -6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![169, 0, 0], ![-71, 1, 0]] ![![169, 0, 0], ![-52, 1, 0]]
  ![![169, 0, 0], ![-26, 46, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![28561, 0, 0], ![-8788, 169, 0]], ![![-11999, 169, 0], ![3692, -123, 1]]]
 hmul := by decide
 f := ![![![![10001342053, -135990192, 0], ![-3078140579, 3097, 0]], ![![26060263140, 0, 0], ![-523393, 0, 0]]], ![![![-1540425964, 20945471, 0], ![474101311, -477, 0]], ![![-4013852042, 0, 0], ![80614, 0, 0]]]]
 g := ![![![![169, 0, 0], ![0, 0, 0]], ![![-26, -45, -1], ![169, 0, 0]]], ![![![-45, -45, -1], ![169, 0, 0]], ![![22, -1, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![169, 0, 0], ![-26, 46, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
