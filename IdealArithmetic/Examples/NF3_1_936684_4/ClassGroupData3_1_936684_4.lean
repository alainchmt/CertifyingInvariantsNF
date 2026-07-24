import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_936684_4.RI3_1_936684_4

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![3, 1, 0]

def alpha1 := B.equivFun.symm ![33, 11, 1]

def alpha2 := B.equivFun.symm ![2, 0, 0]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![401, 6, -4]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![25, 0, 0], ![3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-10, 5, 0]], ![![-10, 5, 0], ![4, -4, 1]]]
 hmul := by decide
 f := ![![![![-2752005, 1522543, -72250], ![-6774975, 305070, 0]], ![![0, 0, 0], ![280100, -200, 0]]], ![![![-302727, 167484, -7948], ![-745263, 33560, 0]], ![![0, 0, 0], ![30812, -22, 0]]]]
 g := ![![![![40, 13, 0], ![-325, 0, 0]], ![![-22, -10, -1], ![180, 25, 0]]], ![![![-22, -10, -1], ![180, 25, 0]], ![![4, 1, 0], ![-32, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![3, 1, 0]] ![![5, 0, 0], ![-2, 1, 0]]
  ![![3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![-50, 25, 0]], ![![15, 5, 0], ![-6, 1, 1]]]
 hmul := by decide
 f := ![![![![-2947181, 1610856, -55892], ![-7348695, 311368, 0]], ![![77030, -165698, 0], ![30812, -22, 0]]]]
 g := ![![![![-75, -3, 1]], ![![100, 3, -1]]], ![![![5, 0, 0]], ![![-2, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![25, 0, 0], ![-3, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![10, 5, 0], ![4, 4, 1]]]
 hmul := by decide
 f := ![![![![-364165, -218453, -18090], ![884125, 76470, 0]], ![![0, 0, 0], ![70100, -50, 0]]], ![![![58243, 34938, 2893], ![-141403, -12229, 0]], ![![0, 0, 0], ![-11212, 8, 0]]]]
 g := ![![![![58, -19, 0], ![475, 0, 0]], ![![28, -9, 0], ![230, 0, 0]]], ![![![28, -9, 0], ![230, 0, 0]], ![![10, -3, 0], ![82, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![25, 0, 0], ![-3, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![33, 11, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![125, 0, 0], ![50, 25, 0]], ![![-15, 5, 0], ![-6, -1, 1]]]
 hmul := by decide
 f := ![![![![-357815, -371854, -147865], ![855955, 649470, 0]], ![![-154330, 436920, 0], ![61732, -44, 0]]]]
 g := ![![![![-325, -13, 4]], ![![150, -3, -1]]], ![![![95, 2, -1]], ![![-32, 3, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
def J2 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ20 : IdealMulEqCertificate timesTableO (J2) J2
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0], ![-56, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![0, 0, 1]]]
 hmul := by decide
 f := ![![![![263, 50, 0], ![26, 0, 0]], ![![0, 0, 0], ![0, -3, 0]]], ![![![-7364, -1412, 0], ![-706, 0, 0]], ![![0, 0, 0], ![1, 84, 0]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![0, 0, 0]], ![![28, 2, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ21 : IdealMulEqCertificate timesTableO (J2*J2) J2
  ![![2, 0, 0], ![-56, -4, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2, 0, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ20
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![-112, -8, 2], ![350, 28, -4]]]
 hmul := by decide
 f := ![![![![-87, 48, -6], ![-222, 6, 2]], ![![0, 0, 0], ![-3, 0, 0]]]]
 g := ![![![![2, 0, 0]], ![![0, 1, 0]]], ![![![-56, -4, 1]], ![![175, 14, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J2_pow3 : J2 ^ 3 = Ideal.span {alpha2} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ21, alpha2]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![9601, 3194, 296])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_0J2_1 : J0 ^ 0*J1 ^ 0*J2 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_0J2_2 : J0 ^ 0*J1 ^ 0*J2 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-56, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ20]
 rfl     

lemma PowJ0_0J1_1J2_0 : J0 ^ 0*J1 ^ 1*J2 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR011_J1_1J2_1 : IdealMulEqCertificate timesTableO (J1) J2
  ![![5, 0, 0], ![2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![10, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![0, 5, 0]], ![![4, 2, 0], ![0, 2, 1]]]
 hmul := by decide
 f := ![![![![-3, 0, 9], ![12, -10, 0]], ![![10, -20, 0], ![0, 0, 0]]], ![![![-3, -2, 0], ![1, 0, 0]], ![![8, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-1, 0, 0], ![5, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_0J1_1J2_1 : J0 ^ 0*J1 ^ 1*J2 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR011_J1_1J2_1]
 rfl
def MulR012_J1_1J2_2 : IdealMulEqCertificate timesTableO (J1) (J2*J2)
  ![![5, 0, 0], ![2, 1, 0]] ![![2, 0, 0], ![-56, -4, 1]]
  ![![10, 0, 0], ![-52, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ20
 M := ![![![10, 0, 0], ![-280, -20, 5]], ![![4, 2, 0], ![238, 20, -2]]]
 hmul := by decide
 f := ![![![![41, 44, 23], ![2, 0, 0]], ![![40, -120, 0], ![0, 0, 0]]], ![![![50, -204, -121], ![-1, 0, 0]], ![![-208, 608, 0], ![0, 0, 0]]]]
 g := ![![![![39, 8, 2], ![-60, -10, 0]], ![![-300, -160, -68], ![1765, 270, 0]]], ![![![-28, -3, 0], ![8, 2, 0]], ![![287, 138, 57], ![-1484, -228, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_0J1_1J2_2 : J0 ^ 0*J1 ^ 1*J2 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-52, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR012_J1_1J2_2]
 rfl

lemma PowJ0_0J1_2J2_0 : J0 ^ 0*J1 ^ 2*J2 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![-3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     
def MulR021_J1_2J2_1 : IdealMulEqCertificate timesTableO ((J1*J1)) J2
  ![![25, 0, 0], ![-3, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![50, 0, 0], ![22, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![50, 0, 0], ![0, 25, 0]], ![![-6, 2, 0], ![0, -3, 1]]]
 hmul := by decide
 f := ![![![![-125, 840, 0], ![420, -672, 0]], ![![-1050, 8400, 0], ![0, 0, 0]]], ![![![-55, 367, 0], ![185, -294, 0]], ![![-462, 3675, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-11, 0, 0], ![25, 0, 0]]], ![![![-1, 0, 0], ![2, 0, 0]], ![![11, 0, 0], ![-25, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_0J1_2J2_1 : J0 ^ 0*J1 ^ 2*J2 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![22, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR021_J1_2J2_1]
 rfl
def MulR022_J1_2J2_2 : IdealMulEqCertificate timesTableO ((J1*J1)) (J2*J2)
  ![![25, 0, 0], ![-3, 1, 0]] ![![2, 0, 0], ![-56, -4, 1]]
  ![![50, 0, 0], ![-72, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ20
 M := ![![![50, 0, 0], ![-1400, -100, 25]], ![![-6, 2, 0], ![518, 40, -7]]]
 hmul := by decide
 f := ![![![![-69, 1054, -337], ![2, 0, 0]], ![![-1050, 8400, 0], ![0, 0, 0]]], ![![![152, -1504, 481], ![-1, 0, 0]], ![![1512, -12012, 0], ![0, 0, 0]]]]
 g := ![![![![16818, 938, -234], ![11800, 25, 0]], ![![-463240, -25736, 6434], ![-321675, 0, 0]]], ![![![-2031, -111, 28], ![-1352, 12, 0]], ![![171333, 9522, -2380], ![119081, 22, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_0J1_2J2_2 : J0 ^ 0*J1 ^ 2*J2 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![-72, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR022_J1_2J2_2]
 rfl

lemma PowJ0_1J1_0J2_0 : J0 ^ 1*J1 ^ 0*J2 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR101_J0_1J2_1 : IdealMulEqCertificate timesTableO (J0) J2
  ![![5, 0, 0], ![-2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![10, 0, 0], ![-2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![0, 5, 0]], ![![-4, 2, 0], ![0, -2, 1]]]
 hmul := by decide
 f := ![![![![-15, 32, 0], ![16, -32, 0]], ![![-40, 80, 0], ![0, 0, 0]]], ![![![3, -8, 0], ![-3, 8, 0]], ![![8, -20, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![1, 0, 0], ![5, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![0, 0, 0], ![0, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_0J2_1 : J0 ^ 1*J1 ^ 0*J2 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR101_J0_1J2_1]
 rfl
def MulR102_J0_1J2_2 : IdealMulEqCertificate timesTableO (J0) (J2*J2)
  ![![5, 0, 0], ![-2, 1, 0]] ![![2, 0, 0], ![-56, -4, 1]]
  ![![10, 0, 0], ![-56, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ20
 M := ![![![10, 0, 0], ![-280, -20, 5]], ![![-4, 2, 0], ![462, 36, -6]]]
 hmul := by decide
 f := ![![![![41, 44, -17], ![2, 0, 0]], ![![-40, 80, 0], ![0, 0, 0]]], ![![![56, -220, 87], ![-1, 0, 0]], ![![224, -432, 0], ![0, 0, 0]]]]
 g := ![![![![197, 68, 37], ![-1090, -180, 0]], ![![-5194, -1856, -1021], ![30015, 4950, 0]]], ![![![-69, -29, -17], ![494, 81, 0]], ![![8673, 3066, 1680], ![-49422, -8154, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_0J2_2 : J0 ^ 1*J1 ^ 0*J2 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-56, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR102_J0_1J2_2]
 rfl
def MulR110_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![5, 0, 0], ![-54, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![-10, 5, 0], ![-4, 0, 1]]]
 hmul := by decide
 f := ![![![![-279, -164, -16], ![671, 84, 0]], ![![-19, 0, 0], ![-20, 0, 0]]], ![![![2962, 1735, 167], ![-7122, -878, 0]], ![![202, 0, 0], ![216, 0, 0]]]]
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![2, 1, 0], ![0, 0, 0]]], ![![![52, 6, -1], ![5, 0, 0]], ![![10, 1, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1J2_0 : J0 ^ 1*J1 ^ 1*J2 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-54, -5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR110_J0_1J1_1]
 rfl
def MulR111_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![5, 0, 0], ![-54, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![-10, 5, 0], ![-4, 0, 1]]]
 hmul := by decide
 f := ![![![![-279, -164, -16], ![671, 84, 0]], ![![-19, 0, 0], ![-20, 0, 0]]], ![![![2962, 1735, 167], ![-7122, -878, 0]], ![![202, 0, 0], ![216, 0, 0]]]]
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![2, 1, 0], ![0, 0, 0]]], ![![![52, 6, -1], ![5, 0, 0]], ![![10, 1, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide
def MulR111_J0_1J1_1J2_1 : IdealMulEqCertificate timesTableO (J0 * J1) J2
  ![![5, 0, 0], ![-54, -5, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![10, 0, 0], ![-54, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR111_J0_1J1_1
 hI2 := rfl
 M := ![![![10, 0, 0], ![0, 5, 0]], ![![-108, -10, 2], ![350, 30, -5]]]
 hmul := by decide
 f := ![![![![55, 4, 0], ![2, -2, 0]], ![![5, 0, 0], ![0, 0, 0]]], ![![![-122, -66, 8], ![161, -5, -1]], ![![-27, 0, 0], ![0, 0, 0]]]]
 g := ![![![![37, -1, 2], ![-110, -18, 0]], ![![18, 0, 1], ![-55, -9, 0]]], ![![![-216, 32, -28], ![1362, 216, 0]], ![![854, -88, 87], ![-4340, -693, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1J2_1 : J0 ^ 1*J1 ^ 1*J2 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-54, -5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR111_J0_1J1_1J2_1]
 rfl
def MulR112_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![5, 0, 0], ![-2, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![5, 0, 0], ![-54, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![10, 5, 0]], ![![-10, 5, 0], ![-4, 0, 1]]]
 hmul := by decide
 f := ![![![![-279, -164, -16], ![671, 84, 0]], ![![-19, 0, 0], ![-20, 0, 0]]], ![![![2962, 1735, 167], ![-7122, -878, 0]], ![![202, 0, 0], ![216, 0, 0]]]]
 g := ![![![![5, 0, 0], ![0, 0, 0]], ![![2, 1, 0], ![0, 0, 0]]], ![![![52, 6, -1], ![5, 0, 0]], ![![10, 1, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide
def MulR112_J0_1J1_1J2_2 : IdealMulEqCertificate timesTableO (J0 * J1) (J2*J2)
  ![![5, 0, 0], ![-54, -5, 1]] ![![2, 0, 0], ![-56, -4, 1]]
  ![![10, 0, 0], ![-54, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR112_J0_1J1_1
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ20
 M := ![![![10, 0, 0], ![-280, -20, 5]], ![![-108, -10, 2], ![-126, 90, -6]]]
 hmul := by decide
 f := ![![![![-1, 1, 0], ![-2, 0, 0]], ![![5, 0, 0], ![0, 0, 0]]], ![![![11, -5, 0], ![11, 0, 0]], ![![-27, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-1, -2, 0], ![5, 0, 0]]], ![![![0, -1, 0], ![2, 0, 0]], ![![9, 9, -1], ![4, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1J2_2 : J0 ^ 1*J1 ^ 1*J2 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-54, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR112_J0_1J1_1J2_2]
 rfl
def MulR120_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![5, 0, 0], ![-2, 1, 0]] ![![25, 0, 0], ![-3, 1, 0]]
  ![![25, 0, 0], ![-44, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![125, 0, 0], ![-15, 5, 0]], ![![-50, 25, 0], ![6, -5, 1]]]
 hmul := by decide
 f := ![![![![18788, -6351, 27], ![156155, -655, 0]], ![![111, 0, 0], ![-100, 0, 0]]], ![![![-33306, 11265, -50], ![-276820, 1215, 0]], ![![-197, 0, 0], ![176, 0, 0]]]]
 g := ![![![![3401, 395, 41], ![-6025, -1000, 0]], ![![-371, -43, -6], ![760, 122, 0]]], ![![![-1386, -160, -17], ![2475, 410, 0]], ![![174, 20, 2], ![-299, -50, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2J2_0 : J0 ^ 1*J1 ^ 2*J2 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![-44, -5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR120_J0_1J1_2]
 rfl
def MulR121_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![5, 0, 0], ![-2, 1, 0]] ![![25, 0, 0], ![-3, 1, 0]]
  ![![25, 0, 0], ![-44, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![125, 0, 0], ![-15, 5, 0]], ![![-50, 25, 0], ![6, -5, 1]]]
 hmul := by decide
 f := ![![![![18788, -6351, 27], ![156155, -655, 0]], ![![111, 0, 0], ![-100, 0, 0]]], ![![![-33306, 11265, -50], ![-276820, 1215, 0]], ![![-197, 0, 0], ![176, 0, 0]]]]
 g := ![![![![3401, 395, 41], ![-6025, -1000, 0]], ![![-371, -43, -6], ![760, 122, 0]]], ![![![-1386, -160, -17], ![2475, 410, 0]], ![![174, 20, 2], ![-299, -50, 0]]]]
 hle1 := by decide
 hle2 := by decide
def MulR121_J0_1J1_2J2_1 : IdealMulEqCertificate timesTableO (J0 * (J1*J1)) J2
  ![![25, 0, 0], ![-44, -5, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![50, 0, 0], ![-44, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR121_J0_1J1_2
 hI2 := rfl
 M := ![![![50, 0, 0], ![0, 25, 0]], ![![-88, -10, 2], ![350, 40, -5]]]
 hmul := by decide
 f := ![![![![209750, 580440, -77378], ![-1598072, 58034, 10963]], ![![1208650, -75, 0], ![0, 0, 0]]], ![![![-182032, -503058, 67060], ![1384903, -50293, -9500]], ![![-1047512, 65, 0], ![0, 0, 0]]]]
 g := ![![![![2280035, 261737, -17470], ![-2032950, -581290, 0]], ![![-150899, -17322, 1156], ![134575, 38475, 0]]], ![![![-3952560, -453735, 30285], ![3524252, 1007700, 0]], ![![15719000, 1804466, -120442], ![-14015500, -4007519, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2J2_1 : J0 ^ 1*J1 ^ 2*J2 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![-44, -5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR121_J0_1J1_2J2_1]
 rfl
def MulR122_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![5, 0, 0], ![-2, 1, 0]] ![![25, 0, 0], ![-3, 1, 0]]
  ![![25, 0, 0], ![-44, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![125, 0, 0], ![-15, 5, 0]], ![![-50, 25, 0], ![6, -5, 1]]]
 hmul := by decide
 f := ![![![![18788, -6351, 27], ![156155, -655, 0]], ![![111, 0, 0], ![-100, 0, 0]]], ![![![-33306, 11265, -50], ![-276820, 1215, 0]], ![![-197, 0, 0], ![176, 0, 0]]]]
 g := ![![![![3401, 395, 41], ![-6025, -1000, 0]], ![![-371, -43, -6], ![760, 122, 0]]], ![![![-1386, -160, -17], ![2475, 410, 0]], ![![174, 20, 2], ![-299, -50, 0]]]]
 hle1 := by decide
 hle2 := by decide
def MulR122_J0_1J1_2J2_2 : IdealMulEqCertificate timesTableO (J0 * (J1*J1)) (J2*J2)
  ![![25, 0, 0], ![-44, -5, 1]] ![![2, 0, 0], ![-56, -4, 1]]
  ![![50, 0, 0], ![752, 80, -13]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR122_J0_1J1_2
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ20
 M := ![![![50, 0, 0], ![-1400, -100, 25]], ![![-88, -10, 2], ![-686, 50, 4]]]
 hmul := by decide
 f := ![![![![-10239, 238674, -27417], ![-202938, 0, 0]], ![![3221150, -200, 0], ![0, 0, 0]]], ![![![-153924, 3570518, -410146], ![-3035985, 0, 0]], ![![48188496, -2992, 0], ![0, 0, 0]]]]
 g := ![![![![2042, -10370, -134], ![22100, 3675, 0]], ![![-71618, 287410, 3989], ![-614875, -102410, 0]]], ![![![-5181, 17941, 262], ![-38494, -6419, 0]], ![![-35933, 142141, 1982], ![-304168, -50666, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2J2_2 : J0 ^ 1*J1 ^ 2*J2 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![752, 80, -13]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR122_J0_1J1_2J2_2]
 rfl

lemma PowJ0_2J1_0J2_0 : J0 ^ 2*J1 ^ 0*J2 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![3, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR201_J0_2J2_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J2
  ![![25, 0, 0], ![3, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![50, 0, 0], ![-22, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![50, 0, 0], ![0, 25, 0]], ![![6, 2, 0], ![0, 3, 1]]]
 hmul := by decide
 f := ![![![![-125, 420, 0], ![210, 378, 0]], ![![1050, -4725, 0], ![0, 0, 0]]], ![![![55, -187, 0], ![-93, -168, 0]], ![![-462, 2100, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![11, 0, 0], ![25, 0, 0]]], ![![![1, 0, 0], ![2, 0, 0]], ![![11, 0, 0], ![25, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_0J2_1 : J0 ^ 2*J1 ^ 0*J2 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![-22, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR201_J0_2J2_1]
 rfl
def MulR202_J0_2J2_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J2*J2)
  ![![25, 0, 0], ![3, 1, 0]] ![![2, 0, 0], ![-56, -4, 1]]
  ![![50, 0, 0], ![-46, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ20
 M := ![![![50, 0, 0], ![-1400, -100, 25]], ![![6, 2, 0], ![182, 16, -1]]]
 hmul := by decide
 f := ![![![![-125, 2100, 714], ![0, 0, 0]], ![![1050, -17850, 0], ![0, 0, 0]]], ![![![143, -1920, -654], ![1, 0, 0]], ![![-966, 16338, 0], ![0, 0, 0]]]]
 g := ![![![![2126, 181, -48], ![2500, 25, 0]], ![![-60541, -5264, 1316], ![-65775, 0, 0]]], ![![![223, 17, -6], ![364, 16, 0]], ![![7845, 679, -172], ![8683, 21, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_0J2_2 : J0 ^ 2*J1 ^ 0*J2 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![-46, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR202_J0_2J2_2]
 rfl
def MulR210_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![3, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![25, 0, 0], ![-49, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![50, 25, 0]], ![![15, 5, 0], ![6, 5, 1]]]
 hmul := by decide
 f := ![![![![3089109, 1858543, 158604], ![-7674289, -792956, 0]], ![![-161570, -300, 0], ![-100, 0, 0]]], ![![![-6024329, -3624502, -309308], ![14966271, 1546415, 0]], ![![315090, 586, 0], ![196, 0, 0]]]]
 g := ![![![![33017, 3040, 312], ![-65300, -11500, 0]], ![![12910, 1190, 121], ![-25450, -4485, 0]]], ![![![3936, 363, 36], ![-7685, -1357, 0]], ![![1538, 142, 14], ![-2994, -529, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1J2_0 : J0 ^ 2*J1 ^ 1*J2 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![-49, -5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR210_J0_2J1_1]
 rfl
def MulR211_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![3, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![25, 0, 0], ![-49, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![50, 25, 0]], ![![15, 5, 0], ![6, 5, 1]]]
 hmul := by decide
 f := ![![![![3089109, 1858543, 158604], ![-7674289, -792956, 0]], ![![-161570, -300, 0], ![-100, 0, 0]]], ![![![-6024329, -3624502, -309308], ![14966271, 1546415, 0]], ![![315090, 586, 0], ![196, 0, 0]]]]
 g := ![![![![33017, 3040, 312], ![-65300, -11500, 0]], ![![12910, 1190, 121], ![-25450, -4485, 0]]], ![![![3936, 363, 36], ![-7685, -1357, 0]], ![![1538, 142, 14], ![-2994, -529, 0]]]]
 hle1 := by decide
 hle2 := by decide
def MulR211_J0_2J1_1J2_1 : IdealMulEqCertificate timesTableO ((J0*J0) * J1) J2
  ![![25, 0, 0], ![-49, -5, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![50, 0, 0], ![-74, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR211_J0_2J1_1
 hI2 := rfl
 M := ![![![50, 0, 0], ![0, 25, 0]], ![![-98, -10, 2], ![350, 35, -5]]]
 hmul := by decide
 f := ![![![![135675, 308460, -40898], ![-899570, 30674, 6425]], ![![630025, -1800, 0], ![0, 0, 0]]], ![![![-199049, -452409, 59982], ![1319343, -44985, -9423]], ![![-924037, 2640, 0], ![0, 0, 0]]]]
 g := ![![![![78652271, -4446827, -1256159], ![-115985750, -35758740, 0]], ![![-5242482, 296403, 83728], ![7730975, 2383475, 0]]], ![![![-152061415, 8597228, 2428580], ![224239802, 69133760, 0]], ![![543226336, -30712844, -8675893], ![-801077175, -246974364, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1J2_1 : J0 ^ 2*J1 ^ 1*J2 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![-74, -5, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR211_J0_2J1_1J2_1]
 rfl
def MulR212_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![25, 0, 0], ![3, 1, 0]] ![![5, 0, 0], ![2, 1, 0]]
  ![![25, 0, 0], ![-49, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![50, 25, 0]], ![![15, 5, 0], ![6, 5, 1]]]
 hmul := by decide
 f := ![![![![3089109, 1858543, 158604], ![-7674289, -792956, 0]], ![![-161570, -300, 0], ![-100, 0, 0]]], ![![![-6024329, -3624502, -309308], ![14966271, 1546415, 0]], ![![315090, 586, 0], ![196, 0, 0]]]]
 g := ![![![![33017, 3040, 312], ![-65300, -11500, 0]], ![![12910, 1190, 121], ![-25450, -4485, 0]]], ![![![3936, 363, 36], ![-7685, -1357, 0]], ![![1538, 142, 14], ![-2994, -529, 0]]]]
 hle1 := by decide
 hle2 := by decide
def MulR212_J0_2J1_1J2_2 : IdealMulEqCertificate timesTableO ((J0*J0) * J1) (J2*J2)
  ![![25, 0, 0], ![-49, -5, 1]] ![![2, 0, 0], ![-56, -4, 1]]
  ![![50, 0, 0], ![-594, -40, 11]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR212_J0_2J1_1
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ20
 M := ![![![50, 0, 0], ![-1400, -100, 25]], ![![-98, -10, 2], ![-406, 70, -1]]]
 hmul := by decide
 f := ![![![![-3142, 102497, -8104], ![-120114, 0, 0]], ![![1680025, -4800, 0], ![0, 0, 0]]], ![![![37626, -1213535, 95944], ![1422165, 0, 0]], ![![-19891497, 56832, 0], ![0, 0, 0]]]]
 g := ![![![![573, 180, 52], ![-600, -100, 0]], ![![-1139, -4010, -1719], ![17925, 2780, 0]]], ![![![409, -247, -129], ![1292, 194, 0]], ![![-64, -1171, -516], ![5349, 826, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1J2_2 : J0 ^ 2*J1 ^ 1*J2 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![-594, -40, 11]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR212_J0_2J1_1J2_2]
 rfl
def MulR220_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![25, 0, 0], ![3, 1, 0]] ![![25, 0, 0], ![-3, 1, 0]]
  ![![25, 0, 0], ![-59, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![625, 0, 0], ![-75, 25, 0]], ![![75, 25, 0], ![-9, 0, 1]]]
 hmul := by decide
 f := ![![![![-203266664, 68582818, -298497], ![-1693035979, 7462439, 0]], ![![852846, 0, 0], ![-350, 0, 0]]], ![![![479703478, -161853473, 704443], ![3995516193, -17611108, 0]], ![![-2012692, 0, 0], ![826, 0, 0]]]]
 g := ![![![![25, 0, 0], ![0, 0, 0]], ![![56, 1, -1], ![25, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2J2_0 : J0 ^ 2*J1 ^ 2*J2 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![-59, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR220_J0_2J1_2]
 rfl
def MulR221_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![25, 0, 0], ![3, 1, 0]] ![![25, 0, 0], ![-3, 1, 0]]
  ![![25, 0, 0], ![-59, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![625, 0, 0], ![-75, 25, 0]], ![![75, 25, 0], ![-9, 0, 1]]]
 hmul := by decide
 f := ![![![![-203266664, 68582818, -298497], ![-1693035979, 7462439, 0]], ![![852846, 0, 0], ![-350, 0, 0]]], ![![![479703478, -161853473, 704443], ![3995516193, -17611108, 0]], ![![-2012692, 0, 0], ![826, 0, 0]]]]
 g := ![![![![25, 0, 0], ![0, 0, 0]], ![![56, 1, -1], ![25, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide
def MulR221_J0_2J1_2J2_1 : IdealMulEqCertificate timesTableO ((J0*J0) * (J1*J1)) J2
  ![![25, 0, 0], ![-59, 0, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![50, 0, 0], ![-506, -25, 9]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR221_J0_2J1_2
 hI2 := rfl
 M := ![![![50, 0, 0], ![0, 25, 0]], ![![-118, 0, 2], ![350, 25, 0]]]
 hmul := by decide
 f := ![![![![-50, 0, -18], ![-336, 14, 4]], ![![275, 0, 0], ![0, 0, 0]]], ![![![-1328, -3, 178], ![2525, -133, -30]], ![![-2783, 0, 0], ![0, 0, 0]]]]
 g := ![![![![617, 2065, 658], ![-6650, -1078, 0]], ![![304, 108, 25], ![-275, -49, 0]]], ![![![-853, -4851, -1566], ![15778, 2548, 0]], ![![4117, 14538, 4640], ![-46875, -7595, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2J2_1 : J0 ^ 2*J1 ^ 2*J2 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![-506, -25, 9]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR221_J0_2J1_2J2_1]
 rfl
def MulR222_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![25, 0, 0], ![3, 1, 0]] ![![25, 0, 0], ![-3, 1, 0]]
  ![![25, 0, 0], ![-59, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![625, 0, 0], ![-75, 25, 0]], ![![75, 25, 0], ![-9, 0, 1]]]
 hmul := by decide
 f := ![![![![-203266664, 68582818, -298497], ![-1693035979, 7462439, 0]], ![![852846, 0, 0], ![-350, 0, 0]]], ![![![479703478, -161853473, 704443], ![3995516193, -17611108, 0]], ![![-2012692, 0, 0], ![826, 0, 0]]]]
 g := ![![![![25, 0, 0], ![0, 0, 0]], ![![56, 1, -1], ![25, 0, 0]]], ![![![3, 1, 0], ![0, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide
def MulR222_J0_2J1_2J2_2 : IdealMulEqCertificate timesTableO ((J0*J0) * (J1*J1)) (J2*J2)
  ![![25, 0, 0], ![-59, 0, 1]] ![![2, 0, 0], ![-56, -4, 1]]
  ![![50, 0, 0], ![-34, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR222_J0_2J1_2
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ20
 M := ![![![50, 0, 0], ![-1400, -100, 25]], ![![-118, 0, 2], ![1904, 250, -31]]]
 hmul := by decide
 f := ![![![![-188, -18, 0], ![12, 3, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![58, -112, -4], ![-49, 0, 2]], ![![13, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-4, -1, 0], ![25, -1, 0]]], ![![![-1, 0, 0], ![2, 0, 0]], ![![17, 5, 0], ![-31, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2J2_2 : J0 ^ 2*J1 ^ 2*J2 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![50, 0, 0], ![-34, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR222_J0_2J1_2J2_2]
 rfl
