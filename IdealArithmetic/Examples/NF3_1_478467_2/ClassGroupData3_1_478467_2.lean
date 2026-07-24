import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_478467_2.RI3_1_478467_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-163, -5, 1]

def alpha1 := B.equivFun.symm ![-40031, -2444, 324]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![58482001, 5144580, -574830]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-119, -7, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-119, -7, 1]] ![![2, 0, 0], ![-119, -7, 1]]
  ![![-163, -5, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-238, -14, 2]], ![![-238, -14, 2], ![1015, 85, -9]]]
 hmul := by decide
 f := ![![![![129, -1022, 18], ![698, 0, 0]], ![![0, 0, 0], ![163, 0, 0]]]]
 g := ![![![![-121, -31, -2]], ![![-782, -201, -13]]], ![![![-782, -201, -13]], ![![-5116, -1307, -84]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-119, -6, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![5, 0, 0], ![-119, -6, 1]] ![![5, 0, 0], ![-119, -6, 1]]
  ![![-40031, -2444, 324]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-595, -30, 5]], ![![-595, -30, 5], ![2893, 207, -22]]]
 hmul := by decide
 f := ![![![![-9702, -294179, -11020], ![583574, 0, 0]], ![![0, 0, 0], ![120093, 0, 0]]]]
 g := ![![![![115033, 29468, 1900]], ![![655385, 167890, 10825]]], ![![![655385, 167890, 10825]], ![![3733969, 956531, 61674]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![36725588227801, 9407994932520, 606596809230])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-119, -6, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-119, -7, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![-119, -7, 1]] ![![5, 0, 0], ![-119, -6, 1]]
  ![![10, 0, 0], ![-119, -11, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![10, 0, 0], ![-238, -12, 2]], ![![-595, -35, 5], ![1954, 146, -16]]]
 hmul := by decide
 f := ![![![![1, 5, 0], ![-25, 0, 0]], ![![10, 0, 0], ![0, 0, 0]]], ![![![0, -60, 0], ![298, 0, 0]], ![![-119, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 1, 0], ![2, 0, 0]]], ![![![0, 2, 0], ![5, 0, 0]], ![![5, -3, 0], ![-16, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![10, 0, 0], ![-119, -11, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
