import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_797203_1.RI3_1_797203_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-122, -3, -4]

def alpha1 := B.equivFun.symm ![6663723, -429182, -637843]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![114822808316479, -34061766327500, 7968395209052]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![-122, -3, -4]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![2, -1, 4]]]
 hmul := by decide
 f := ![![![![-22, -26, 16], ![42, 22, 0]], ![![0, 0, 0], ![-61, 0, 0]]]]
 g := ![![![![5, -1, 0]], ![![-1, 3, -2]]], ![![![-1, 3, -2]], ![![-149, 24, 4]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![3, 0, 0], ![18, -1, 1]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![3, 0, 0], ![18, -1, 1]] ![![3, 0, 0], ![18, -1, 1]]
  ![![6663723, -429182, -637843]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![9, 0, 0], ![54, -3, 3]], ![![54, -3, 3], ![123, 40, 11]]]
 hmul := by decide
 f := ![![![![1406920, 11473965, 994509], ![4948409, 0, 0]], ![![0, 0, 0], ![-2221241, 0, 0]]]]
 g := ![![![![55631015622020, 1376544129793, 1820709559793]], ![![371661237705289, 9196454339624, 12163847108099]]], ![![![371661237705289, 9196454339624, 12163847108099]], ![![2483004742375251, 61439928143464, 81264568351050]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-139404895225512259695722594033, -3449460486051777097413370100, -4562487716268939269605048396])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![3, 0, 0], ![18, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![3, 0, 0], ![18, -1, 1]]
  ![![6, 0, 0], ![36, 1, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![6, 0, 0], ![36, -2, 2]], ![![0, 3, 0], ![150, -7, -2]]]
 hmul := by decide
 f := ![![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![0, 0, 0]]], ![![![0, 1, 0], ![1, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]]
 g := ![![![![1, 0, 0], ![0, 0, 0]], ![![18, 0, 1], ![-2, 0, 0]]], ![![![-18, 0, -1], ![3, 0, 0]], ![![-5, -2, -2], ![5, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![6, 0, 0], ![36, 1, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
