import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_677484_9.RI3_1_677484_9

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-119, 33, -9]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![15252391, 473190, -463011]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![11, 0, 0], ![4, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![11, 0, 0], ![4, 1, 0]] ![![11, 0, 0], ![4, 1, 0]]
  ![![121, 0, 0], ![-29, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![121, 0, 0], ![44, 11, 0]], ![![44, 11, 0], ![16, 8, 6]]]
 hmul := by decide
 f := ![![![![23586653, 6799961, 1366728], ![-58963003, -1071598, 0]], ![![0, 0, 0], ![-15734114, -5082, 0]]], ![![![-5685493, -1639112, -329448], ![14212859, 258310, 0]], ![![0, 0, 0], ![3792658, 1225, 0]]]]
 g := ![![![![3075, -106, 0], ![12826, 0, 0]], ![![1134, -39, 0], ![4730, 0, 0]]], ![![![1134, -39, 0], ![4730, 0, 0]], ![![444, -15, 0], ![1852, 1, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![121, 0, 0], ![-29, 1, 0]] ![![11, 0, 0], ![4, 1, 0]]
  ![![-119, 33, -9]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![1331, 0, 0], ![484, 121, 0]], ![![-319, 11, 0], ![-116, -25, 6]]]
 hmul := by decide
 f := ![![![![-4980500752, 196975386, -700804089], ![12158400978, 701407470, 0]], ![![-2306964135, 6424035039, 0], ![-72851499, 5229, 0]]]]
 g := ![![![![-37651, -7410, -2547]], ![![-73430, -14453, -4968]]], ![![![3593, 707, 243]], ![![7006, 1379, 474]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![10166555695645, 2001026105913, 687826765545])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![11, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![121, 0, 0], ![-29, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
