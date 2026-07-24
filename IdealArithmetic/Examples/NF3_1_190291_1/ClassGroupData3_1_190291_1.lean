import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_190291_1.RI3_1_190291_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-11, -1, -1]

def alpha1 := B.equivFun.symm ![-23, -2, -2]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-20, 5, -3]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![2, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![2, 1, 8]]]
 hmul := by decide
 f := ![![![![-5979, -9360, -23254], ![12760, 5990, 6]], ![![0, 0, 0], ![-332, 0, 4]]], ![![![-2979, -4662, -11585], ![6355, 2984, 3]], ![![0, 0, 0], ![-165, 0, 2]]]]
 g := ![![![![6428, -1204, 95], ![2916, 0, -380]], ![![-68, 13, -1], ![-30, 0, 4]]], ![![![-68, 13, -1], ![-30, 0, 4]], ![![3179, -596, 49], ![1445, 0, -188]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![4, 0, 0], ![2, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![-11, -1, -1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![8, 0, 0], ![0, 4, 0]], ![![4, 2, 0], ![2, 3, 8]]]
 hmul := by decide
 f := ![![![![4277246, 7053144, 17111524], ![-9837704, -4278544, -1992]], ![![16557, 0, 3633], ![804, 0, 11]]]]
 g := ![![![![7, -1, 0]], ![![-1, 3, -4]]], ![![![3, 1, -2]], ![![-82, 7, 5]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![9, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![0, 3, 0]], ![![0, 3, 0], ![2, 1, 8]]]
 hmul := by decide
 f := ![![![![1455, 105266, -4840], ![-318057, -14175, 0]], ![![0, 0, 0], ![47970, -36, 0]]], ![![![-82, -5846, 264], ![17662, 789, 0]], ![![0, 0, 0], ![-2664, 2, 0]]]]
 g := ![![![![-9, -5, -40], ![0, 45, 0]], ![![0, 0, 0], ![3, 0, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![-2, -1, -8], ![0, 10, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ11 : IdealMulEqCertificate timesTableO (J1*J1) J1
  ![![9, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![-23, -2, -2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 hI2 := rfl
 M := ![![![27, 0, 0], ![0, 9, 0]], ![![0, 3, 0], ![2, 1, 8]]]
 hmul := by decide
 f := ![![![![-22069, 4573218, -79590], ![-13606180, -113474, 0]], ![![-428876, 469048, 0], ![-117262, 88, 0]]]]
 g := ![![![![3, -2, 2]], ![![54, -3, -6]]], ![![![18, -1, -2]], ![![-56, 9, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow3 : J1 ^ 3 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ11, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-2494, -224, -215])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_0J1_2 : J0 ^ 0*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10]
 rfl     

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![6, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![6, 0, 0], ![0, 2, 0]], ![![0, 3, 0], ![2, 1, 8]]]
 hmul := by decide
 f := ![![![![250, -2358, -3], ![6894, 0, 0]], ![![90, 0, -6], ![0, 0, 0]]], ![![![0, 0, 0], ![2, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]]
 g := ![![![![0, -46, -337], ![-6, 252, -6]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![3, 0, 0]], ![![0, -16, -111], ![3, 84, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
def MulR12_J0_1J1_2 : IdealMulEqCertificate timesTableO (J0) (J1*J1)
  ![![2, 0, 0], ![0, 1, 0]] ![![9, 0, 0], ![0, 1, 0]]
  ![![18, 0, 0], ![0, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![18, 0, 0], ![0, 2, 0]], ![![0, 9, 0], ![2, 1, 8]]]
 hmul := by decide
 f := ![![![![-20196, -10789, -83785], ![-1197, 94248, 0]], ![![810, 0, -18], ![0, 0, 0]]], ![![![0, 0, 0], ![5, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]]
 g := ![![![![0, -47, -337], ![0, 756, -18]], ![![0, 0, 0], ![2, 0, 0]]], ![![![0, 0, 0], ![9, 0, 0]], ![![0, -6, -37], ![15, 84, -2]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_2 : J0 ^ 1*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![18, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR12_J0_1J1_2]
 rfl

lemma PowJ0_2J1_0 : J0 ^ 2*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![2, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
def MulR21_J0_2J1_1 : IdealMulEqCertificate timesTableO ((J0*J0)) J1
  ![![4, 0, 0], ![2, 1, 0]] ![![3, 0, 0], ![0, 1, 0]]
  ![![12, 0, 0], ![6, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![12, 0, 0], ![0, 4, 0]], ![![6, 3, 0], ![2, 3, 8]]]
 hmul := by decide
 f := ![![![![5348422, -118978020, -3771069], ![364839093, 1414467, 0]], ![![-12442860, 0, -3372], ![0, 0, 0]]], ![![![2671040, -59418472, -1883299], ![182203246, 706395, 0]], ![![-6214053, 0, -1684], ![0, 0, 0]]]]
 g := ![![![![930, -27921, -31069], ![-1860, 47316, -1140]], ![![-8, 196, 218], ![16, -332, 8]]], ![![![456, -13814, -15371], ![-912, 23409, -564]], ![![146, -4507, -5014], ![-292, 7637, -184]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_1 : J0 ^ 2*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![12, 0, 0], ![6, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR21_J0_2J1_1]
 rfl
def MulR22_J0_2J1_2 : IdealMulEqCertificate timesTableO ((J0*J0)) (J1*J1)
  ![![4, 0, 0], ![2, 1, 0]] ![![9, 0, 0], ![0, 1, 0]]
  ![![36, 0, 0], ![18, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10
 M := ![![![36, 0, 0], ![0, 4, 0]], ![![18, 9, 0], ![2, 3, 8]]]
 hmul := by decide
 f := ![![![![-29761128684, -14699440886, -120934102657], ![-1633271202, 136050873984, 0]], ![![-943544268, 0, -30204], ![0, 0, 0]]], ![![![-14878593765, -7348747147, -60459043905], ![-816527459, 68016428640, 0]], ![![-471709659, 0, -15100], ![0, 0, 0]]]]
 g := ![![![![828, -75346, -29929], ![-1656, 141948, -3420]], ![![-8, 176, 70], ![16, -332, 8]]], ![![![414, -37276, -14807], ![-828, 70227, -1692]], ![![38, -4054, -1610], ![-76, 7637, -184]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_2J1_2 : J0 ^ 2*J1 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![36, 0, 0], ![18, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR22_J0_2J1_2]
 rfl
