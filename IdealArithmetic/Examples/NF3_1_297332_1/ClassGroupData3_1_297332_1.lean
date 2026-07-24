import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_297332_1.RI3_1_297332_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-50, 10, -1]

def alpha1 := B.equivFun.symm ![-3, -1, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![753, -2092, 402]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-22, -2, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-22, -2, 1]] ![![2, 0, 0], ![-22, -2, 1]]
  ![![4, 0, 0], ![-22, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-44, -4, 2]], ![![-44, -4, 2], ![-132, 25, -1]]]
 hmul := by decide
 f := ![![![![27589, -7533, 55545], ![-268053, -39078, 0]], ![![0, 0, 0], ![-1002, 6, 0]]], ![![![-151734, 41452, -305611], ![1474832, 215007, 0]], ![![0, 0, 0], ![5513, -33, 0]]]]
 g := ![![![![23, -1, 8], ![-80, -12, 0]], ![![-132, 18, -84], ![818, 120, 0]]], ![![![-132, 18, -84], ![818, 120, 0]], ![![-594, 73, -328], ![3195, 471, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![-22, -2, 1]] ![![2, 0, 0], ![-22, -2, 1]]
  ![![-50, 10, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![-88, -8, 4]], ![![-44, -4, 2], ![-132, 25, -1]]]
 hmul := by decide
 f := ![![![![-1369703839, 797657851, -2704436470], ![12916866151, 1844227350, 0]], ![![-260207150, 488085, 0], ![12515, -75, 0]]]]
 g := ![![![![-1765, -577, -115]], ![![-7304, -2388, -476]]], ![![![-3652, -1194, -238]], ![![-15114, -4942, -985]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![25, 0, 0], ![3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-10, 5, 0], ![4, -4, 2]]]
 hmul := by decide
 f := ![![![![-3632085, 1992083, -173400], ![-8941575, 359320, 0]], ![![0, 0, 0], ![369700, -300, 0]]], ![![![-399539, 219136, -19076], ![-983597, 39530, 0]], ![![0, 0, 0], ![40668, -33, 0]]]]
 g := ![![![![40, 13, 0], ![-325, 0, 0]], ![![-22, -10, -2], ![180, 25, 0]]], ![![![-22, -10, -2], ![180, 25, 0]], ![![4, 1, 0], ![-32, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![25, 0, 0], ![3, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![-3, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![125, 0, 0], ![-50, 25, 0]], ![![15, 5, 0], ![-6, 1, 2]]]
 hmul := by decide
 f := ![![![![3890117, -2112822, 134120], ![9699875, -377427, 0]], ![![-101670, 218762, 0], ![-40668, 33, 0]]]]
 g := ![![![![61, 3, -2]], ![![-86, -3, 2]]], ![![![-5, 0, 0]], ![![2, -1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![42880385, 14018784, 2794082])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-22, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![-22, -2, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![10, 0, 0], ![-18, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![-4, 2, 0]], ![![-110, -10, 5], ![198, 17, -6]]]
 hmul := by decide
 f := ![![![![8265, -4288, 372], ![19670, -975, 0]], ![![36, 0, 0], ![0, 0, 0]]], ![![![-1522202, 790007, -68791], ![-3622708, 180279, 0]], ![![-6633, 2, 0], ![0, 0, 0]]]]
 g := ![![![![149, 16, 10], ![-260, -40, 0]], ![![-58, -6, -5], ![122, 18, 0]]], ![![![-1548, -167, -110], ![2825, 430, 0]], ![![2818, 304, 197], ![-5076, -775, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-18, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![-22, -2, 1]] ![![25, 0, 0], ![3, 1, 0]]
  ![![50, 0, 0], ![2, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![50, 0, 0], ![6, 2, 0]], ![![-550, -50, 25], ![88, 7, -1]]]
 hmul := by decide
 f := ![![![![2533913, 852919, 8276], ![-20918300, -116925, 0]], ![![2156, 0, 0], ![0, 0, 0]]], ![![![-404101446, -136021258, -1319881], ![3335992742, 18647519, 0]], ![![-343833, 2, 0], ![0, 0, 0]]]]
 g := ![![![![40607, 9818, -1081], ![1250, -13200, 0]], ![![4805, 1162, -128], ![152, -1562, 0]]], ![![![-445004, -107571, 11837], ![-13225, 144650, 0]], ![![71234, 17220, -1895], ![2129, -23155, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![2, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![-22, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![-22, -2, 1]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![20, 0, 0], ![-18, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![20, 0, 0], ![-8, 4, 0]], ![![-110, -10, 5], ![198, 17, -6]]]
 hmul := by decide
 f := ![![![![17750793547, -9496914211, 832417984], ![43410356500, -2124982455, 0]], ![![70299752, -60, 0], ![0, 0, 0]]], ![![![-14201410871, 7597946560, -665970782], ![-34730183024, 1700078872, 0]], ![![-56242875, 48, 0], ![0, 0, 0]]]]
 g := ![![![![459, 51, -30], ![680, 20, 0]], ![![-282, -31, 12], ![-176, 16, 0]]], ![![![-2809, -312, 156], ![-3115, 0, 0]], ![![5096, 566, -284], ![5694, 5, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![-18, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![-22, -2, 1]] ![![25, 0, 0], ![3, 1, 0]]
  ![![100, 0, 0], ![2, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![100, 0, 0], ![12, 4, 0]], ![![-550, -50, 25], ![88, 7, -1]]]
 hmul := by decide
 f := ![![![![110644739575087, 37382613881770, 389214206288], ![-918080104538500, -5135136115825, 0]], ![![86386730712, -300, 0], ![0, 0, 0]]], ![![![4425597918566, 1495239799207, 15567894034], ![-36721613836554, -205396549278, 0]], ![![3455319585, -12, 0], ![0, 0, 0]]]]
 g := ![![![![82981, 19969, -2169], ![1300, -53900, 0]], ![![9889, 2381, -259], ![204, -6424, 0]]], ![![![-455556, -109619, 11904], ![-6775, 295900, 0]], ![![72904, 17545, -1906], ![1179, -47355, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100, 0, 0], ![2, -2, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
