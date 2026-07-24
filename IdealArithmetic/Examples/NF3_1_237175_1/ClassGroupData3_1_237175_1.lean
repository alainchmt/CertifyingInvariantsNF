import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_237175_1.RI3_1_237175_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![393, 203, 305]

def alpha1 := B.equivFun.symm ![2142, 1681, -508]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-2557889622582653, -2370981285422604, 1980077510206602]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![17, -1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![17, -1, 1]] ![![2, 0, 0], ![17, -1, 1]]
  ![![393, 203, 305]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![34, -2, 2]], ![![34, -2, 2], ![319, -7, 11]]]
 hmul := by decide
 f := ![![![![534, 1181, -661], ![3636, 0, 0]], ![![0, 0, 0], ![-393, 0, 0]]]]
 g := ![![![![-14980566, 521153, -615829]], ![![-134962754, 4695166, -5548120]]], ![![![-134962754, 4695166, -5548120]], ![![-1215904991, 42299639, -49984063]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
def J1 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)))
def MulJ10 : IdealMulEqCertificate timesTableO (J1) J1
  ![![2, 0, 0], ![0, 1, 0]] ![![2, 0, 0], ![0, 1, 0]]
  ![![2142, 1681, -508]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![0, 2, 0], ![2, -1, 4]]]
 hmul := by decide
 f := ![![![![0, 550, -1198], ![276, 0, 0]], ![![0, 0, 0], ![1071, 0, 0]]]]
 g := ![![![![97442509, -3389889, 4005718]], ![![-67481377, 2347583, -2774060]]], ![![![-67481377, 2347583, -2774060]], ![![46732543, -1625760, 1921106]]]]
 hle1 := by decide
 hle2 := by decide

lemma J1_pow2 : J1 ^ 2 = Ideal.span {alpha1} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ10, alpha1]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![2616581606496066983895117011269051, -91027225145102087613060339666516, 107563815291628968368614970617242])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_0J1_1 : J0 ^ 0*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![0, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_1J1_0 : J0 ^ 1*J1 ^ 0 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![17, -1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
def MulR11_J0_1J1_1 : IdealMulEqCertificate timesTableO (J0) J1
  ![![2, 0, 0], ![17, -1, 1]] ![![2, 0, 0], ![0, 1, 0]]
  ![![4, 0, 0], ![34, 0, 2]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![0, 2, 0]], ![![34, -2, 2], ![-34, -6, -2]]]
 hmul := by decide
 f := ![![![![42, -6, -17], ![16, 10, 0]], ![![-6, 0, 0], ![0, 0, 0]]], ![![![190, -63, -280], ![87, 156, -6]], ![![-51, 0, 0], ![0, 0, 0]]]]
 g := ![![![![-16, 0, -1], ![2, 0, 0]], ![![-3, 11, -6], ![6, 3, 0]]], ![![![-14, -11, 5], ![-3, -3, 0]], ![![-8, -33, 17], ![-17, -9, 0]]]]
 hle1 := by decide
 hle2 := by decide

lemma PowJ0_1J1_1 : J0 ^ 1*J1 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![4, 0, 0], ![34, 0, 2]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulR11_J0_1J1_1]
 rfl
