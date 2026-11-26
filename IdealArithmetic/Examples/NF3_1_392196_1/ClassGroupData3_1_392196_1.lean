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
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-15, 1, -1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![-15, 1, -1]] ![![3, 0, 0], ![-15, 1, -1]]
  ![![3, 0, 0], ![13, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-45, 3, -3]], ![![-45, 3, -3], ![113, 18, 11]]]
 hmul := by decide
 f := ![![![![-550054, -20247054, 4490309], ![-5495500, 0, -2367248]], ![![0, 0, 0], ![-7787, 0, -4]]], ![![![-2337755, -86050629, 19083957], ![-23356053, 0, -10060880]], ![![0, 0, 0], ![-33095, 0, -17]]]]
 g := ![![![![-10, 0, -1], ![3, 0, 0]], ![![-2, 1, 0], ![-3, 0, 0]]], ![![![-2, 1, 0], ![-3, 0, 0]], ![![-10, 6, 0], ![11, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![3, 0, 0], ![13, 0, 1]] ![![3, 0, 0], ![-15, 1, -1]]
  ![![178715, 1854, 7664]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![9, 0, 0], ![-45, 3, -3]], ![![39, 0, 3], ![-161, -15, -5]]]
 hmul := by decide
 f := ![![![![-17939185, -660537836, 146236838], ![-179228939, 0, -77204880]], ![![0, 0, 0], ![178715, 0, 0]]]]
 g := ![![![![-157, 26, 24]], ![![381, -233, 151]]], ![![![381, -30, -99]], ![![-2247, 1001, -431]]]]
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


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-15, 1, -1]] i)) := by 
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
  ![![2, 0, 0], ![15, 0, 1]] ![![3, 0, 0], ![-15, 1, -1]]
  ![![6, 0, 0], ![17, -2, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![6, 0, 0], ![-30, 2, -2]], ![![45, 0, 3], ![-191, -13, -7]]]
 hmul := by decide
 f := ![![![![-159, -5905, 1308], ![-1605, 0, -690]], ![![-6, 0, 0], ![0, 0, 0]]], ![![![-13233, -489134, 108344], ![-132960, 0, -57155]], ![![-497, -2, 0], ![0, 0, 0]]]]
 g := ![![![![9182, 6232, -12915], ![21786, -5580, 12]], ![![-47443, -32198, 66727], ![-112560, 28830, -62]]], ![![![68865, 46740, -96862], ![163395, -41850, 90]], ![![-282349, -191636, 397135], ![-669919, 171585, -369]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![17, -2, 1]] i)) := by 
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
  ![![4, 0, 0], ![15, 0, 1]] ![![3, 0, 0], ![-15, 1, -1]]
  ![![12, 0, 0], ![-9, -5, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![12, 0, 0], ![-60, 4, -4]], ![![45, 0, 3], ![-191, -13, -7]]]
 hmul := by decide
 f := ![![![![-1035, -38419, 8508], ![-10407, 0, -4488]], ![![-36, 0, 0], ![0, 0, 0]]], ![![![-313165, -11496683, 2545797], ![-3114983, 0, -1343034]], ![![-10773, -15, 0], ![0, 0, 0]]]]
 g := ![![![![106008, -62128, 48093], ![-57612, 19836, 12]], ![![-530064, 310700, -240490], ![288148, -99192, -60]]], ![![![397512, -232990, 180347], ![-216069, 74385, 45]], ![![-1686976, 988809, -765374], ![917025, -315684, -191]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![-9, -5, -1]] i)) := by 
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
