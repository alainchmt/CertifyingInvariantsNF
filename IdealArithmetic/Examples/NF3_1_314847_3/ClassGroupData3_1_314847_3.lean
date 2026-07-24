import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_314847_3.RI3_1_314847_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-818, -255, 136]

def alpha1 := B.equivFun.symm ![-84405, -14150, -6818]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-564937179, 236816362, -69827960]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![2, -1, 4]]]
 hmul := by decide
 f := ![![![![-29132, 22809, -57603], ![-16650, 29040, 8]], ![![0, 0, 0], ![-444, 0, -4]]], ![![![-14663, 11436, -28885], ![-8355, 14562, 5]], ![![0, 0, 0], ![-223, 0, -2]]]]
 g := ![![![![8072, -382, -950], ![3713, 1235, -380]], ![![-86, 4, 9], ![-38, -12, 4]]], ![![![-86, 4, 9], ![-38, -12, 4]], ![![4077, -194, -479], ![1879, 624, -192]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![-818, -255, 136]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![4, 2, 0], ![2, 1, 4]]]
 hmul := by decide
 f := ![![![![508655958, -404213544, 1017436984], ![300124100, -508725268, -46920]], ![![-1031157, 0, 114573], ![-105777, 0, 818]]]]
 g := ![![![![-1677751, -281265, -135524]], ![![-7802847, -1308101, -630292]]], ![![![-4740299, -794683, -382908]], ![![-22046077, -3695894, -1780820]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![-1, 1, 0]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![25, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-5, 5, 0]], ![![-5, 5, 0], ![3, -3, 4]]]
 hmul := by decide
 f := ![![![![739930, -737625, 1602232], ![-295509, -2023872, 0]], ![![0, 0, 0], ![105170, -120, 0]]], ![![![117157, -116792, 253688], ![-46785, -320448, 0]], ![![0, 0, 0], ![16652, -19, 0]]]]
 g := ![![![![-1395, -2154, -2888], ![-300, 18050, 0]], ![![291, 453, 608], ![80, -3800, 0]]], ![![![291, 453, 608], ![80, -3800, 0]], ![![-185, -284, -380], ![-31, 2376, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![25, 0, 0], ![4, 1, 0]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![-84405, -14150, -6818]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![125, 0, 0], ![-25, 25, 0]], ![![20, 5, 0], ![-2, 2, 4]]]
 hmul := by decide
 f := ![![![![-61019337043, 46446811834, -106887605814], ![21493229780, 133879425464, 0]], ![![74312923032, -1458025358, 0], ![540963231, 402314, 0]]]]
 g := ![![![![4231, -470, 6]], ![![-901, 1045, -376]]], ![![![666, 115, -74]], ![![-1730, -46, 92]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1336060994325026213, 223982698111255754, 107923243619917896])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![10, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![-2, 2, 0]], ![![0, 5, 0], ![2, -2, 4]]]
 hmul := by decide
 f := ![![![![535, 2245, -175], ![345, 225, 0]], ![![-4358, 0, -10], ![0, 0, 0]]], ![![![214, 898, -70], ![138, 90, 0]], ![![-1743, 0, -4], ![0, 0, 0]]]]
 g := ![![![![60, -54, -75], ![30, 200, -10]], ![![-16, 10, 15], ![4, -40, 2]]], ![![![-2, 0, 0], ![5, 0, 0]], ![![8, -16, -21], ![8, 56, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![0, 1, 0]] ![![25, 0, 0], ![4, 1, 0]]
  ![![50, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![50, 0, 0], ![8, 2, 0]], ![![0, 25, 0], ![2, 3, 4]]]
 hmul := by decide
 f := ![![![![-81662342, -126613102, -169131963], ![-18130475, 1057074925, 0]], ![![979110, 0, -50], ![0, 0, 0]]], ![![![-6532852, -10128834, -13530270], ![-1450387, 84564200, 0]], ![![78327, 0, -4], ![0, 0, 0]]]]
 g := ![![![![622786, 940885, 1256337], ![68650, -15704150, -50]], ![![99610, 150489, 200944], ![10994, -2511790, -8]]], ![![![-437, -655, -874], ![0, 10925, 0]], ![![24855, 37551, 50141], ![2748, -626759, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![20, 0, 0], ![-6, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![20, 0, 0], ![-4, 4, 0]], ![![10, 5, 0], ![0, 0, 4]]]
 hmul := by decide
 f := ![![![![3341543773, 1767012531, -3196575], ![-314906245, 4048995, 0]], ![![-6809135284, 0, -56828], ![0, 0, 0]]], ![![![-1002674817, -530215699, 959175], ![94491824, -1214955, 0]], ![![2043171941, 0, 17052], ![0, 0, 0]]]]
 g := ![![![![59726, 1036, 0], ![-17853, -14335, -11468]], ![![-12016, -209, 0], ![3607, 2885, 2308]]], ![![![29773, 516, 0], ![-8886, -7145, -5716]], ![![2, 0, 0], ![7, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![20, 0, 0], ![-6, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![2, 1, 0]] ![![25, 0, 0], ![4, 1, 0]]
  ![![100, 0, 0], ![-46, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![100, 0, 0], ![16, 4, 0]], ![![50, 25, 0], ![10, 5, 4]]]
 hmul := by decide
 f := ![![![![-11261421813893862, -17393642418018012, -23326057133151303], ![-2497573186943725, 145787857088843175, 0]], ![![-3990007898420, 0, -1418140], ![0, 0, 0]]], ![![![5180282621930285, 8001119666698013, 10730045495315247], ![1148890006176769, -67062784348778175, 0]], ![![1835413762057, 0, 652348], ![0, 0, 0]]]]
 g := ![![![![62076, -297710, 0], ![-31465, -645075, -57340]], ![![9926, -47559, 0], ![-5006, -103050, -9160]]], ![![![30965, -148388, 0], ![-15630, -321525, -28580]], ![![6187, -29677, 0], ![-3139, -64304, -5716]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![100, 0, 0], ![-46, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
