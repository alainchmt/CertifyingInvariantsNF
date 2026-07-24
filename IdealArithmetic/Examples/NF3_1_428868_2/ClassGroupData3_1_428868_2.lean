import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_428868_2.RI3_1_428868_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![3, -1, 0]

def alpha1 := B.equivFun.symm ![60, -14, -7]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-81483, 23174, 5134]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![20, 1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![20, 1, 1]] ![![2, 0, 0], ![20, 1, 1]]
  ![![2, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![40, 2, 2]], ![![40, 2, 2], ![495, 45, 12]]]
 hmul := by decide
 f := ![![![![2229998, -16101621, -4673082], ![11912781, -2545968, 0]], ![![0, 0, 0], ![-3422, -3, 0]]], ![![![2229354, -16096915, -4671716], ![11909299, -2545224, 0]], ![![0, 0, 0], ![-3421, -3, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![16, -3, 1], ![8, 0, 0]]], ![![![16, -3, 1], ![8, 0, 0]], ![![202, -23, 6], ![91, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![20, 1, 1]]
  ![![3, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0], ![40, 2, 2]], ![![2, 2, 0], ![115, -7, 2]]]
 hmul := by decide
 f := ![![![![452, -3315, -959], ![2443, -522, 0]], ![![0, 0, 0], ![-3, 0, 0]]]]
 g := ![![![![33, 2, 1]], ![![425, 25, 13]]], ![![![64, 4, 2]], ![![830, 49, 25]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![0, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![0, 1, 0]] ![![5, 0, 0], ![0, 1, 0]]
  ![![25, 0, 0], ![5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![0, 5, 0]], ![![0, 5, 0], ![0, 1, 2]]]
 hmul := by decide
 f := ![![![![875, -11598, -23598], ![-2316, 60306, 0]], ![![0, 0, 0], ![-6555, -115, 0]]], ![![![175, -2318, -4716], ![-462, 12052, 0]], ![![0, 0, 0], ![-1310, -23, 0]]]]
 g := ![![![![-4, 215, 72], ![25, -900, 0]], ![![-1, -216, -72], ![5, 900, 0]]], ![![![-1, -216, -72], ![5, 900, 0]], ![![-4, -55, -18], ![20, 226, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![25, 0, 0], ![5, 1, 0]] ![![5, 0, 0], ![0, 1, 0]]
  ![![60, -14, -7]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![125, 0, 0], ![0, 25, 0]], ![![25, 5, 0], ![0, 6, 2]]]
 hmul := by decide
 f := ![![![![0, 16481629, 34996535], ![3296330, -87848445, 0]], ![![2100, 1774320, 0], ![57464, -276, 0]]]]
 g := ![![![![-66642, -3976, -2037]], ![![-38703, -2309, -1183]]], ![![![-21069, -1257, -644]], ![![-12236, -730, -374]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-66048060687, -3940539274, -2018832366])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![20, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![20, 1, 1]] ![![5, 0, 0], ![0, 1, 0]]
  ![![10, 0, 0], ![20, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![0, 2, 0]], ![![100, 5, 5], ![95, -8, 1]]]
 hmul := by decide
 f := ![![![![-6344, 2284, 5265], ![460, -14040, 0]], ![![720, -18, 0], ![0, 0, 0]]], ![![![-12678, 4565, 10521], ![914, -28056, 0]], ![![1439, -36, 0], ![0, 0, 0]]]]
 g := ![![![![351, -212, -50], ![680, -180, 0]], ![![-15, 2, 0], ![-2, 2, 0]]], ![![![3520, -2119, -499], ![6795, -1800, 0]], ![![3360, -2025, -477], ![6490, -1719, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![20, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![20, 1, 1]] ![![25, 0, 0], ![5, 1, 0]]
  ![![50, 0, 0], ![40, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![50, 0, 0], ![10, 2, 0]], ![![500, 25, 25], ![195, -3, 6]]]
 hmul := by decide
 f := ![![![![827231, -129505753, -43241283], ![-5014775, 540404100, 0]], ![![18000, -90, 0], ![0, 0, 0]]], ![![![661736, -103597171, -34590545], ![-4011526, 432292269, 0]], ![![14399, -72, 0], ![0, 0, 0]]]]
 g := ![![![![5950861, 1139415, 7251], ![4783650, -5146200, 0]], ![![1185280, 226948, 1444], ![952818, -1025018, 0]]], ![![![59446270, 11382197, 72437], ![47786175, -51408000, 0]], ![![23215360, 4445056, 28288], ![18661825, -20076219, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![40, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![2, 0, 0], ![1, 1, 0]] ![![5, 0, 0], ![0, 1, 0]]
  ![![10, 0, 0], ![5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![10, 0, 0], ![0, 2, 0]], ![![5, 5, 0], ![0, 2, 2]]]
 hmul := by decide
 f := ![![![![0, -1, 0], ![0, 0, 0]], ![![2, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![-2, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-1, 0, 0], ![2, 0, 0]]], ![![![-2, 0, 0], ![5, 0, 0]], ![![2, 0, 0], ![-4, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![2, 0, 0], ![1, 1, 0]] ![![25, 0, 0], ![5, 1, 0]]
  ![![50, 0, 0], ![5, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![50, 0, 0], ![10, 2, 0]], ![![25, 25, 0], ![5, 7, 2]]]
 hmul := by decide
 f := ![![![![1451, -183328, -61218], ![-7025, 765225, 0]], ![![-90, 0, 0], ![0, 0, 0]]], ![![![142, -18436, -6156], ![-687, 76950, 0]], ![![-9, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![-2, 0, 0], ![25, 0, 0]], ![![0, 0, 0], ![1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![5, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
