import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_648324_3.RI3_1_648324_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-1409, -363, -49]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![496546942937207, 25310875074642, -7940967232216]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-53, -4, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![-53, -4, 1]] ![![2, 0, 0], ![-53, -4, 1]]
  ![![2, 0, 0], ![-53, -3, 1]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![-106, -8, 2]], ![![-106, -8, 2], ![-599, -11, 7]]]
 hmul := by decide
 f := ![![![![1345552, -6315252, 1447760], ![-22301504, 0, 687804]], ![![0, 0, 0], ![42176, 0, 9]]], ![![![-35880096, 168406805, -38606955], ![594706788, 0, -18341439]], ![![0, 0, 0], ![-1124693, 0, -240]]]]
 g := ![![![![2, 0, 0], ![0, 0, 0]], ![![0, -1, 0], ![2, 0, 0]]], ![![![0, -1, 0], ![2, 0, 0]], ![![45, 14, -3], ![13, 0, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![2, 0, 0], ![-53, -3, 1]] ![![2, 0, 0], ![-53, -4, 1]]
  ![![-1409, -363, -49]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![4, 0, 0], ![-106, -8, 2]], ![![-106, -6, 2], ![-173, 17, -1]]]
 hmul := by decide
 f := ![![![![66442, -295917, 70666], ![-1132841, 0, 35385]], ![![0, 0, 0], ![-1409, 0, 0]]]]
 g := ![![![![478, 27, -8]], ![![-100, -134, 19]]], ![![![-1804, -219, 46]], ![![-38033, -2011, 618]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-3351701503201147042323139225, -863520962827278908497644834, -116567989976268685288393904])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-53, -4, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![-53, -3, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
