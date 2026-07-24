import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_392196_1.RI3_1_392196_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![11, -4, 1]

def alpha1 := B.equivFun.symm ![178715, 1854, 7664]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-30419, -4583, 16498]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![15, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![15, 0, 1]] ![![2, 0, 0], ![15, 0, 1]]
  ![![4, 0, 0], ![15, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![30, 0, 2]], ![![30, 0, 2], ![271, 6, 9]]]
 hmul := by decide
 f := ![![![![-28, 132, 49], ![-152, 36, 0]], ![![0, 0, 0], ![-4, 0, 0]]], ![![![-90, 495, 185], ![-572, 135, 0]], ![![0, 0, 0], ![-15, 0, 0]]]]
 g := ![![![![-14, 0, -1], ![4, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-11, 12, 2], ![-11, 6, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![15, 0, 1]] ![![2, 0, 0], ![15, 0, 1]]
  ![![11, -4, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![60, 0, 4]], ![![30, 0, 2], ![271, 6, 9]]]
 hmul := by decide
 f := ![![![![897547, -2440625, -1098006], ![6182702, -683375, 0]], ![![-5199864, -26625, 0], ![2917, 4, 0]]]]
 g := ![![![![-2122, -22, -91]], ![![-18888, -196, -810]]], ![![![-9444, -98, -405]], ![![-84065, -872, -3605]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-14, -1, -1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![-14, -1, -1]] ![![3, 0, 0], ![-14, -1, -1]]
  ![![3, 0, 0], ![13, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-42, -3, -3]], ![![-42, -3, -3], ![404, -12, 17]]]
 hmul := by decide
 f := ![![![![-4216645, 12685798, 6970577], ![13125558, 0, -1558032]], ![![0, 0, 0], ![709, 0, -4]]], ![![![-17919253, 53910180, 29622501], ![55779006, 0, -6621088]], ![![0, 0, 0], ![3013, 0, -17]]]]
 g := ![![![![-10, 0, -1], ![3, 0, 0]], ![![-1, -1, 0], ![-3, 0, 0]]], ![![![-1, -1, 0], ![-3, 0, 0]], ![![-4, -4, -5], ![32, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![3, 0, 0], ![13, 0, 1]] ![![3, 0, 0], ![-14, -1, -1]]
  ![![178715, 1854, 7664]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![9, 0, 0], ![-42, -3, -3]], ![![39, 0, 3], ![-308, 3, -8]]]
 hmul := by decide
 f := ![![![![800949113, -2409512792, -1324154365], ![-2493206743, 0, 295947096]], ![![0, 0, 0], ![178715, 0, 0]]]]
 g := ![![![![-157, 26, 24]], ![![-986, 267, 23]]], ![![![381, -30, -99]], ![![3200, -755, -212]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![147222617615, 1527296303, 6313482748])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-14, -1, -1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![13, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![15, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![15, 0, 1]] ![![3, 0, 0], ![-14, -1, -1]]
  ![![6, 0, 0], ![17, 1, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![6, 0, 0], ![-28, -2, -2]], ![![45, 0, 3], ![-336, 1, -10]]]
 hmul := by decide
 f := ![![![![3742, -11236, -6173], ![-11628, 0, 1380]], ![![-6, 0, 0], ![0, 0, 0]]], ![![![-138975, 418074, 229693], ![432691, 0, -51345]], ![![223, 1, 0], ![0, 0, 0]]]]
 g := ![![![![40940, -48704, 16077], ![110610, -25890, -24]], ![![-184324, 219172, -72355], ![-497736, 116510, 108]]], ![![![307169, -365273, 120585], ![829533, -194175, -180]], ![![-2296951, 2731425, -901705], ![-6203048, 1451995, 1346]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![17, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![15, 0, 1]] ![![3, 0, 0], ![13, 0, 1]]
  ![![6, 0, 0], ![13, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![6, 0, 0], ![26, 0, 2]], ![![45, 0, 3], ![241, 6, 7]]]
 hmul := by decide
 f := ![![![![-6, 0, -1], ![12, 0, 0]], ![![-6, 0, 0], ![0, 0, 0]]], ![![![0, 0, -1], ![23, 0, 0]], ![![-13, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-12, 0, -1], ![6, 0, 0]], ![![0, 0, 0], ![2, 0, 0]]], ![![![1, 0, 0], ![3, 0, 0]], ![![-26, 16, 3], ![-31, 10, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![13, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![15, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![15, 0, 1]] ![![3, 0, 0], ![-14, -1, -1]]
  ![![12, 0, 0], ![69, 1, 5]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![12, 0, 0], ![-56, -4, -4]], ![![45, 0, 3], ![-336, 1, -10]]]
 hmul := by decide
 f := ![![![![24300, -73074, -40153], ![-75606, 0, 8976]], ![![-36, 0, 0], ![0, 0, 0]]], ![![![-1318170, 3965744, 2179128], ![4103232, 0, -487124]], ![![1953, 3, 0], ![0, 0, 0]]]]
 g := ![![![![24174, -88262, -22193], ![122796, -21780, -24]], ![![-113169, 411835, 103528], ![-572916, 101628, 112]]], ![![![90894, -330979, -83206], ![460443, -81675, -90]], ![![-678755, 2471321, 621270], ![-3437978, 609843, 672]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![69, 1, 5]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![15, 0, 1]] ![![3, 0, 0], ![13, 0, 1]]
  ![![12, 0, 0], ![19, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![12, 0, 0], ![52, 0, 4]], ![![45, 0, 3], ![241, 6, 7]]]
 hmul := by decide
 f := ![![![![6, 0, -1], ![30, 0, 0]], ![![-36, 0, 0], ![0, 0, 0]]], ![![![3, 0, -2], ![49, 0, 0]], ![![-57, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-18, 0, -1], ![12, 0, 0]], ![![-2, 0, 0], ![4, 0, 0]]], ![![![-1, 0, 0], ![3, 0, 0]], ![![-3, 0, -1], ![23, -2, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![19, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
