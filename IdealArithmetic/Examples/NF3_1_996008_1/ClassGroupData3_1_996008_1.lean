import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_996008_1.RI3_1_996008_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![499, 83, -21]

def alpha1 := B.equivFun.symm ![-837, -58, 24]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-15687752005, 3528470595, -188015139]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![9, 0, 0], ![-4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-3, 3, 0]], ![![-3, 3, 0], ![1, -2, 1]]]
 hmul := by decide
 f := ![![![![0, 733, -288], ![0, -339, 0]], ![![0, 0, 0], ![3573, -18, 0]]], ![![![0, -406, 159], ![0, 191, 0]], ![![0, 0, 0], ![-1984, 10, 0]]]]
 g := ![![![![37, -9, 0], ![81, 0, 0]], ![![-7, 6, -1], ![-15, 9, 0]]], ![![![-7, 6, -1], ![-15, 9, 0]], ![![5, -1, 0], ![11, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-4, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![27, 0, 0], ![-13, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![-9, 9, 0]], ![![-12, 3, 0], ![4, -5, 1]]]
 hmul := by decide
 f := ![![![![257256, -493181, 56730], ![418041, 97554, 0]], ![![257256, -796176, 0], ![-21438, -54, 0]]], ![![![-133368, 255679, -29411], ![-216723, -50573, 0]], ![![-133368, 412760, 0], ![11114, 28, 0]]]]
 g := ![![![![352, -27, 0], ![729, 0, 0]], ![![-100, 21, -1], ![-207, 27, 0]]], ![![![-142, 24, -1], ![-294, 27, 0]], ![![56, -4, 0], ![116, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![27, 0, 0], ![-13, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![81, 0, 0], ![14, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0, 0], ![-27, 27, 0]], ![![-39, 3, 0], ![13, -14, 1]]]
 hmul := by decide
 f := ![![![![631448, -1159557, 6338], ![1026105, 178152, 0]], ![![578826, -1753812, 0], ![-64314, -162, 0]]], ![![![101364, -186138, 1017], ![164718, 28599, 0]], ![![92916, -281530, 0], ![-10324, -26, 0]]]]
 g := ![![![![351, 25, 0], ![-2025, 0, 0]], ![![-145, -24, -1], ![837, 81, 0]]], ![![![-197, -28, -1], ![1137, 81, 0]], ![![47, 3, 0], ![-271, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ03 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0) J0
  ![![81, 0, 0], ![14, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![243, 0, 0], ![-67, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![243, 0, 0], ![-81, 81, 0]], ![![42, 3, 0], ![-14, 13, 1]]]
 hmul := by decide
 f := ![![![![-350802, 626176, 57891], ![-570051, -72492, 0]], ![![964710, -2761938, 0], ![96471, -486, 0]]], ![![![98164, -175220, -16200], ![159517, 20287, 0]], ![![-269950, 772860, 0], ![-26995, 136, 0]]]]
 g := ![![![![15277, -228, 0], ![55404, 0, 0]], ![![-5003, 142, -1], ![-18144, 243, 0]]], ![![![2748, -41, 0], ![9966, 0, 0]], ![![-782, 79, -1], ![-2836, 244, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ04 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0) J0
  ![![243, 0, 0], ![-67, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![729, 0, 0], ![-67, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![729, 0, 0], ![-243, 243, 0]], ![![-201, 3, 0], ![67, -68, 1]]]
 hmul := by decide
 f := ![![![![-1676490578, 21917416777, 1714380278], ![-2724297189, -6175515306, 0]], ![![-2787047190, 83622492126, 0], ![-578826, -1458, 0]]], ![![![156374674, -2044347244, -159908836], ![254108847, 576021246, 0]], ![![259961850, -7799888692, 0], ![53990, 136, 0]]]]
 g := ![![![![32764, -489, 0], ![356481, 0, 0]], ![![-10832, 229, -1], ![-117855, 729, 0]]], ![![![-8978, 201, -1], ![-97683, 729, 0]], ![![3082, -46, 0], ![33533, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ05 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0) J0
  ![![729, 0, 0], ![-67, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![2187, 0, 0], ![662, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![2187, 0, 0], ![-729, 729, 0]], ![![-201, 3, 0], ![67, -68, 1]]]
 hmul := by decide
 f := ![![![![-5484113246, 71692750649, 5607784642], ![-8911684023, -20200284252, 0]], ![![-27349528500, 820594548900, 0], ![-1736478, -4374, 0]]], ![![![-1657527512, 21668536233, 1694906160], ![-2693482206, -6105367520, 0]], ![![-8266167000, 248017861700, 0], ![-524836, -1322, 0]]]]
 g := ![![![![493191, 745, 0], ![-1629315, 0, 0]], ![![-165721, -912, -1], ![547479, 2187, 0]]], ![![![-46341, -732, -1], ![153093, 2187, 0]], ![![14123, 21, 0], ![-46657, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ06 : IdealMulEqCertificate timesTableO (J0*J0*J0*J0*J0*J0*J0) J0
  ![![2187, 0, 0], ![662, 1, 0]] ![![3, 0, 0], ![-1, 1, 0]]
  ![![499, 83, -21]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![6561, 0, 0], ![-2187, 2187, 0]], ![![1986, 3, 0], ![-662, 661, 1]]]
 hmul := by decide
 f := ![![![![-6559769414, 750117995220, 75471715475], ![-10659625297, -222695503441, 0]], ![![9932606320, -2711619607104, 0], ![165235, -832, 0]]]]
 g := ![![![![-173565, -45901, -6343]], ![![-360783, -95413, -13186]]], ![![![-53112, -14046, -1941]], ![![-110402, -29197, -4035]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow8 : J0 ^ 8 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ06, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![-837, -58, 24]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![0, 0, 1]]]
 hmul := by decide
 f := ![![![![-2645, -296, 0], ![-98, 0, 0]], ![![0, 0, 0], ![24, 116, 0]]]]
 g := ![![![![-247685, -65502, -9052]], ![![-597432, -157995, -21834]]], ![![![-597432, -157995, -21834]], ![![-1441044, -381094, -52665]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-235777612071528545365, -62353010764946278533, -8616827553632317305])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![3, 0, 0], ![-1, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![3, 0, 0], ![-18, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![-3, 3, 0], ![0, -1, 1]]]
 hmul := by decide
 f := ![![![![0, 0, 0], ![1, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]], ![![![0, -2, 0], ![0, 0, 0]], ![![6, 0, 0], ![1, 0, 0]]]]
 g := ![![![![3, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]], ![![![17, 2, -1], ![3, 0, 0]], ![![6, 0, 0], ![1, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-18, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![9, 0, 0], ![-4, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![9, 0, 0], ![-21, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![0, 9, 0]], ![![-12, 3, 0], ![0, -4, 1]]]
 hmul := by decide
 f := ![![![![-33, -12, 0], ![-3, 16, 0]], ![![-75, -48, 0], ![0, 0, 0]]], ![![![77, 17, 0], ![7, -29, 0]], ![![175, 88, 0], ![-2, 0, 0]]]]
 g := ![![![![33, -4, 7], ![-72, -9, 0]], ![![-30, 5, -7], ![72, 9, 0]]], ![![![-13, 4, -6], ![61, 7, 0]], ![![18, -2, 3], ![-30, -4, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-21, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl

lemma PowJ0_3J1_0 : J0 ^ 3*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-13, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
def MulR31_J0_3J1_1 : IdealMulEqCertificate timesTableO (((J0*J0)*J0)) J1
  ![![27, 0, 0], ![-13, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![27, 0, 0], ![-21, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0, 0], ![0, 27, 0]], ![![-39, 3, 0], ![0, -13, 1]]]
 hmul := by decide
 f := ![![![![537, 32, 3], ![50, -5, -8]], ![![18, -36, 0], ![0, 0, 0]]], ![![![-522, -60, -3], ![-8, 8, 8]], ![![13, 10, 0], ![-2, 0, 0]]]]
 g := ![![![![49, 4, -5], ![144, 9, 0]], ![![-17, 2, -2], ![63, 9, 0]]], ![![![-8, 0, 0], ![1, 1, 0]], ![![-11, 0, -1], ![33, 5, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_3J1_1 : J0 ^ 3*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-21, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR31_J0_3J1_1]
 rfl

lemma PowJ0_4J1_0 : J0 ^ 4*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![14, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02]
 rfl     
def MulR41_J0_4J1_1 : IdealMulEqCertificate timesTableO ((((J0*J0)*J0)*J0)) J1
  ![![81, 0, 0], ![14, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![81, 0, 0], ![-48, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02
 hI2 := rfl
 M := ![![![243, 0, 0], ![0, 81, 0]], ![![42, 3, 0], ![0, 14, 1]]]
 hmul := by decide
 f := ![![![![123, 32, 3], ![8, -5, -2]], ![![54, -108, 0], ![0, 0, 0]]], ![![![-268, -16, -3], ![-81, 7, 4]], ![![22, 54, 0], ![1, 0, 0]]]]
 g := ![![![![61311, -10061, 29], ![-36207, -33858, 0]], ![![-2754, 459, -2], ![1701, 1539, 0]]], ![![![10540, -1721, 4], ![-6119, -5795, 0]], ![![-444, 80, -1], ![348, 266, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_4J1_1 : J0 ^ 4*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![81, 0, 0], ![-48, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR41_J0_4J1_1]
 rfl

lemma PowJ0_5J1_0 : J0 ^ 5*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![243, 0, 0], ![-67, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03]
 rfl     
def MulR51_J0_5J1_1 : IdealMulEqCertificate timesTableO (((((J0*J0)*J0)*J0)*J0)) J1
  ![![243, 0, 0], ![-67, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![243, 0, 0], ![-48, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ03
 hI2 := rfl
 M := ![![![729, 0, 0], ![0, 243, 0]], ![![-201, 3, 0], ![0, -67, 1]]]
 hmul := by decide
 f := ![![![![-15633, 124950, 0], ![41652, -6206, 0]], ![![-56700, 502686, 0], ![0, 0, 0]]], ![![![3088, -22293, 0], ![-7428, 1107, 0]], ![![11200, -89666, 0], ![-2, 0, 0]]]]
 g := ![![![![275211, -33435, -1221], ![-54189, -350892, 0]], ![![-3618, 441, 16], ![729, 4617, 0]]], ![![![-75885, 9225, 336], ![15157, 96805, 0]], ![![1026, -121, -5], ![-57, -1273, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_5J1_1 : J0 ^ 5*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![243, 0, 0], ![-48, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR51_J0_5J1_1]
 rfl

lemma PowJ0_6J1_0 : J0 ^ 6*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![729, 0, 0], ![-67, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04]
 rfl     
def MulR61_J0_6J1_1 : IdealMulEqCertificate timesTableO ((((((J0*J0)*J0)*J0)*J0)*J0)) J1
  ![![729, 0, 0], ![-67, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![729, 0, 0], ![-48, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ04
 hI2 := rfl
 M := ![![![2187, 0, 0], ![0, 729, 0]], ![![-201, 3, 0], ![0, -67, 1]]]
 hmul := by decide
 f := ![![![![-42768, 408604, 0], ![136203, -20300, 0]], ![![-465345, 4932900, 0], ![0, 0, 0]]], ![![![2816, -24299, 0], ![-8098, 1207, 0]], ![![30640, -293300, 0], ![-2, 0, 0]]]]
 g := ![![![![284715, -33237, -1419], ![-18225, -1052676, 0]], ![![-3714, 439, 18], ![729, 13851, 0]]], ![![![-26159, 3057, 130], ![2035, 96805, 0]], ![![358, -40, -2], ![186, -1273, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_6J1_1 : J0 ^ 6*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![729, 0, 0], ![-48, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR61_J0_6J1_1]
 rfl

lemma PowJ0_7J1_0 : J0 ^ 7*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2187, 0, 0], ![662, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05]
 rfl     
def MulR71_J0_7J1_1 : IdealMulEqCertificate timesTableO (((((((J0*J0)*J0)*J0)*J0)*J0)*J0)) J1
  ![![2187, 0, 0], ![662, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![2187, 0, 0], ![681, -1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ05
 hI2 := rfl
 M := ![![![6561, 0, 0], ![0, 2187, 0]], ![![1986, 3, 0], ![0, 662, 1]]]
 hmul := by decide
 f := ![![![![-220887, 14692922, 0], ![4897641, 73984, 0]], ![![729729, -53934336, 0], ![0, 0, 0]]], ![![![-68781, 4591538, 0], ![1530514, 23120, 0]], ![![227227, -16854480, 0], ![1, 0, 0]]]]
 g := ![![![![26590350, 103958029, -151009], ![8234055, -322022628, 0]], ![![-47790, -184977, 268], ![-13122, 572994, 0]]], ![![![8048582, 31467609, -45710], ![2493028, -97474742, 0]], ![![-14550, -55992, 81], ![-3702, 173444, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_7J1_1 : J0 ^ 7*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2187, 0, 0], ![681, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR71_J0_7J1_1]
 rfl
