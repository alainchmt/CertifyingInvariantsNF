import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_925444_2.RI3_1_925444_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-715, -2, 17]

def alpha1 := B.equivFun.symm ![-58881025, -13848593, -4125431]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-34776286830037, -686116484889, 1038492391575]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![4, 0, 0], ![1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![2, 2, 0]], ![![2, 2, 0], ![-1, 4, 5]]]
 hmul := by decide
 f := ![![![![-27, 37, 65], ![6, -24, 0]], ![![0, 0, 0], ![-4, 0, 0]]], ![![![-7967, 11153, 19370], ![1594, -7170, 0]], ![![0, 0, 0], ![-1153, -1, 0]]]]
 g := ![![![![7, -9, -15], ![0, 12, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-8, 12, 20], ![1, -15, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![1, 1, 0]] ![![2, 0, 0], ![1, 1, 0]]
  ![![-715, -2, 17]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![4, 4, 0]], ![![2, 2, 0], ![-1, 4, 5]]]
 hmul := by decide
 f := ![![![![380634, -513030, -894001], ![-66196, 347536, 0]], ![![37236, 18618, 0], ![3019, 2, 0]]]]
 g := ![![![![-43232, -10168, -3029]], ![![-362812, -85332, -25420]]], ![![![-181406, -42666, -12710]], ![![-1522397, -358062, -106665]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![9, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![-2, 2, 5]]]
 hmul := by decide
 f := ![![![![104085, -91304, -254420], ![-30432, 166536, 0]], ![![0, 0, 0], ![-41634, -18, 0]]], ![![![-40475, 35504, 98935], ![11837, -64760, 0]], ![![0, 0, 0], ![16190, 7, 0]]]]
 g := ![![![![0, -3, 10], ![9, -18, 0]], ![![3, 1, -5], ![3, 9, 0]]], ![![![3, 1, -5], ![3, 9, 0]], ![![3, 1, -5], ![3, 10, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![9, 0, 0], ![-3, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![-58881025, -13848593, -4125431]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![27, 0, 0], ![0, 9, 0]], ![![-9, 3, 0], ![-2, -1, 5]]]
 hmul := by decide
 f := ![![![![25420995991052, -23327502203554, -64306405010033], ![-7775834067850, 38879170339256, 0]], ![![-891321115061, -966450544472, 0], ![241612636118, 103913457, 0]]]]
 g := ![![![![-39621, 6319, -1369]], ![![-110082, -23597, 10988]]], ![![![-23487, -9972, 4119]], ![![325184, 29459, -17993]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-86996972262995899020516835, -20461356797177761541166603, -6095342366786496186300405])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![6, 0, 0], ![3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![6, 0, 0], ![0, 2, 0]], ![![3, 3, 0], ![-2, 3, 5]]]
 hmul := by decide
 f := ![![![![-252, 262, 685], ![90, -420, 0]], ![![-42, 6, 0], ![0, 0, 0]]], ![![![-90, 94, 245], ![32, -150, 0]], ![![-15, 2, 0], ![0, 0, 0]]]]
 g := ![![![![-69, 175, 175], ![0, -210, 0]], ![![-3, 5, 5], ![2, -6, 0]]], ![![![-39, 95, 95], ![3, -114, 0]], ![![18, -51, -50], ![4, 61, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![1, 1, 0]] ![![9, 0, 0], ![-3, 1, 0]]
  ![![18, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![18, 0, 0], ![-6, 2, 0]], ![![9, 9, 0], ![-5, 0, 5]]]
 hmul := by decide
 f := ![![![![273, 203, -305], ![-63, 468, 0]], ![![-342, 18, 0], ![0, 0, 0]]], ![![![-56, -45, 65], ![23, -99, 0]], ![![75, -4, 0], ![0, 0, 0]]]]
 g := ![![![![-90, -48, 235], ![18, -846, 0]], ![![28, 14, -70], ![2, 252, 0]]], ![![![-60, -31, 155], ![9, -558, 0]], ![![26, 13, -65], ![1, 235, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![18, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![1, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![12, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![12, 0, 0], ![0, 4, 0]], ![![3, 3, 0], ![-2, 3, 5]]]
 hmul := by decide
 f := ![![![![1176, -1174, -3095], ![-390, 1848, 0]], ![![252, 12, 0], ![0, 0, 0]]], ![![![-378, 377, 995], ![127, -594, 0]], ![![-81, -4, 0], ![0, 0, 0]]]]
 g := ![![![![15, 7, -35], ![0, 84, 0]], ![![7, 3, -15], ![4, 36, 0]]], ![![![9, 4, -20], ![3, 48, 0]], ![![3, 1, -5], ![4, 13, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![1, 1, 0]] ![![9, 0, 0], ![-3, 1, 0]]
  ![![36, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![36, 0, 0], ![-12, 4, 0]], ![![9, 9, 0], ![-5, 0, 5]]]
 hmul := by decide
 f := ![![![![3513, 2633, -5795], ![-873, 10188, 0]], ![![-5940, 108, 0], ![0, 0, 0]]], ![![![-388, -291, 640], ![97, -1125, 0]], ![![657, -12, 0], ![0, 0, 0]]]]
 g := ![![![![-270, -138, 685], ![36, -4932, 0]], ![![88, 44, -220], ![4, 1584, 0]]], ![![![-75, -38, 190], ![9, -1368, 0]], ![![38, 19, -95], ![1, 685, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![36, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
