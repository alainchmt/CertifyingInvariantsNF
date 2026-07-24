import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_592328_1.RI3_1_592328_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![602, -99, -52]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![6903131033682962535047941368010, 155870529360192107646040254143, -119072896981337702897609170776]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-17, 0, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![3, 0, 0], ![-17, 0, 1]] ![![3, 0, 0], ![-17, 0, 1]]
  ![![9, 0, 0], ![-14, 0, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![-51, 0, 3]], ![![-51, 0, 3], ![397, -36, -11]]]
 hmul := by decide
 f := ![![![![30, -72, 23], ![-135, 0, 0]], ![![0, 0, 0], ![-18, 0, 0]]], ![![![-24, 112, -37], ![214, 0, 0]], ![![0, 0, 0], ![28, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![-1, 0, 0], ![3, 0, 0]]], ![![![-1, 0, 0], ![3, 0, 0]], ![![13, -4, 1], ![-20, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![9, 0, 0], ![-14, 0, 1]] ![![3, 0, 0], ![-17, 0, 1]]
  ![![27, 0, 0], ![-23, -9, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![27, 0, 0], ![-153, 0, 9]], ![![-42, 0, 3], ![346, -36, -8]]]
 hmul := by decide
 f := ![![![![314, -72, -116], ![-1779, 0, 0]], ![![6237, 0, 0], ![-54, 0, 0]]], ![![![-253, 61, 98], ![1518, 0, 0]], ![![-5313, 0, 0], ![46, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![2, 3, 0], ![9, 0, 0]]], ![![![1, 1, 0], ![3, 0, 0]], ![![29, 5, -1], ![19, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ02 : IdealMulEqCertificate timesTableO (J0*J0*J0) J0
  ![![27, 0, 0], ![-23, -9, 1]] ![![3, 0, 0], ![-17, 0, 1]]
  ![![602, -99, -52]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01
 hI2 := rfl
 M := ![![![81, 0, 0], ![-459, 0, 27]], ![![-69, -27, 3], ![2236, -90, -8]]]
 hmul := by decide
 f := ![![![![593171, 7478511, 260271], ![-3274455, 0, 0]], ![![22439550, 0, 0], ![-1204, 0, 0]]]]
 g := ![![![![-2130, 345, -154]], ![![-15669, 2538, -1133]]], ![![![-11520, 1866, -833]], ![![-84754, 13728, -6128]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow4 : J0 ^ 4 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ02, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![9644158985148381220368939742501149254697305589191376098268862, -1562119839178924406958872249862749546918319185319411429419317, 697327248118213878125437810788073996407916226698777264667310])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![-17, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![9, 0, 0], ![-14, 0, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     

lemma PowJ0_3 : J0 ^ 3 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![27, 0, 0], ![-23, -9, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01]
 rfl     
