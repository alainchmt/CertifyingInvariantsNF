import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_3_895700_1.RI3_3_895700_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![10, -1, 0]

def alpha1 := B.equivFun.symm ![-137, 4, 2]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![6, -1, 0]

def zeta2 := B.equivFun.symm ![132, -13, -3]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![9, 0, 0], ![-1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![2, -2, 2]]]
 hmul := by decide
 f := ![![![![40838, -39469, 102960], ![-26769, -164736, 0]], ![![0, 0, 0], ![30906, 18, 0]]], ![![![-4537, 4385, -11440], ![2976, 18304, 0]], ![![0, 0, 0], ![-3434, -2, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![3, 0, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![0, 0, 0], ![-1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![10, -1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 9, 0]], ![![-3, 3, 0], ![2, -2, 2]]]
 hmul := by decide
 f := ![![![![-1175960, 1176695, -2819450], ![784220, 4312100, 0]], ![![-240468, -265360, 0], ![49784, 29, 0]]]]
 g := ![![![![-82, 9, 2]], ![![-255, 27, 6]]], ![![![-85, 9, 2]], ![![-254, 26, 6]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![19, 0, 0], ![-1, 1, 0]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![361, 0, 0], ![37, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![361, 0, 0], ![-19, 19, 0]], ![![-19, 19, 0], ![2, -2, 2]]]
 hmul := by decide
 f := ![![![![1021481711, -1021365070, 2056915100], ![-107518250, -19568489600, 0]], ![![0, 0, 0], ![528188410, 61560, 0]]], ![![![104686942, -104674988, 210803726], ![-11019039, -2005484096, 0]], ![![0, 0, 0], ![54131590, 6309, 0]]]]
 g := ![![![![4153177, 156928824, 8482768], ![860624, -1531139624, 0]], ![![-219301, -8285063, -447848], ![-45106, 80836564, 0]]], ![![![-219301, -8285063, -447848], ![-45106, 80836564, 0]], ![![23055, 872039, 47138], ![5015, -8508408, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![361, 0, 0], ![37, 1, 0]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![-137, 4, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![6859, 0, 0], ![-361, 361, 0]], ![![703, 19, 0], ![-36, 36, 2]]]
 hmul := by decide
 f := ![![![![-1596278811921911, 1605208004666934, -3218988567519942], ![168499306136261, 30582623699738700, 0]], ![![-42413483543065, -42413847556788, 0], ![-191586170, -23364, 0]]]]
 g := ![![![![1345, -152, -30]], ![![597, -57, -16]]], ![![![173, -19, -4]], ![![80, -8, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![142, -5, -2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![31, -8, 1])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![19, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![361, 0, 0], ![37, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![-1, 1, 0]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![57, 0, 0], ![-1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![57, 0, 0], ![-3, 3, 0]], ![![-19, 19, 0], ![2, -2, 2]]]
 hmul := by decide
 f := ![![![![39, -38, 0], ![0, 0, 0]], ![![114, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![13, 0, 0]], ![![-2, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![3, 0, 0]]], ![![![0, 0, 0], ![19, 0, 0]], ![![0, 0, 0], ![-1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![57, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![3, 0, 0], ![-1, 1, 0]] ![![361, 0, 0], ![37, 1, 0]]
  ![![1083, 0, 0], ![398, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![1083, 0, 0], ![111, 3, 0]], ![![-361, 361, 0], ![-36, 36, 2]]]
 hmul := by decide
 f := ![![![![9275932613568, 350491384736671, 18945768000360], ![1921609117867, -3419711123945128, 0]], ![![721278, -996, 0], ![0, 0, 0]]], ![![![3408626614537, 128795056189978, 6962000666584], ![706133631481, -1256641120274370, 0]], ![![265048, -366, 0], ![0, 0, 0]]]]
 g := ![![![![76807, 40231371, 202168], ![66063, -109473972, 0]], ![![7573, 4123273, 20720], ![7584, -11219880, 0]]], ![![![-25917, -13430092, -67488], ![-21299, 36544752, 0]], ![![-2836, -1340065, -6734], ![-1445, 3646462, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1083, 0, 0], ![398, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![9, 0, 0], ![-1, 1, 0]] ![![19, 0, 0], ![-1, 1, 0]]
  ![![171, 0, 0], ![-1, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![171, 0, 0], ![-9, 9, 0]], ![![-19, 19, 0], ![2, -2, 2]]]
 hmul := by decide
 f := ![![![![153, -152, 0], ![0, 0, 0]], ![![1368, 0, 0], ![0, 0, 0]]], ![![![0, 0, 0], ![17, 0, 0]], ![![-8, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![9, 0, 0]]], ![![![0, 0, 0], ![19, 0, 0]], ![![0, 0, 0], ![-1, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![171, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![9, 0, 0], ![-1, 1, 0]] ![![361, 0, 0], ![37, 1, 0]]
  ![![3249, 0, 0], ![-685, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![3249, 0, 0], ![333, 9, 0]], ![![-361, 361, 0], ![-36, 36, 2]]]
 hmul := by decide
 f := ![![![![1343338996937507, 50758104427125930, 2743722989699472], ![278287111672646, -495241999640275288, 0]], ![![34543368, -11952, 0], ![0, 0, 0]]], ![![![-283234116489945, -10702009615514875, -578495791942552], ![-58674991483768, 104418490445529556, 0]], ![![-7283240, 2520, 0], ![0, 0, 0]]]]
 g := ![![![![74955283, -56121068490, 163857164], ![-33074820, -266185962918, 0]], ![![7682327, -5751793257, 16793560], ![-3388698, -27281138220, 0]]], ![![![-8340323, 6244804107, -18233008], ![3681478, 29619521496, 0]], ![![-831570, 622751882, -1818254], ![367858, 2953753624, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3249, 0, 0], ![-685, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
