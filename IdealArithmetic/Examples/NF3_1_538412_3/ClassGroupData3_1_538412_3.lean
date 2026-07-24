import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_538412_3.RI3_1_538412_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![506, 24, -35]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![3251440, 592688, -486671]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![5, 0, 0], ![-1, 1, 0]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![25, 0, 0], ![4, 1, 0]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![25, 0, 0], ![-5, 5, 0]], ![![-5, 5, 0], ![-1, -4, 10]]]
 hmul := by decide
 f := ![![![![2949960, 330940, 21086], ![-523800, 0, -103200]], ![![0, 0, 0], ![-2225, 0, 100]]], ![![![442494, 49641, 3163], ![-78570, 0, -15480]], ![![0, 0, 0], ![-334, 0, 15]]]]
 g := ![![![![407079, -414249, -2062314], ![48575, 5156025, -400]], ![![-101765, 103555, 515544], ![-12130, -1288920, 100]]], ![![![-101765, 103555, 515544], ![-12130, -1288920, 100]], ![![-7, 5, 28], ![9, -69, 0]]]]
 hle1 := by decide
 hle2 := by decide

def MulJ01 : IdealMulEqCertificate timesTableO (J0*J0) J0
  ![![25, 0, 0], ![4, 1, 0]] ![![5, 0, 0], ![-1, 1, 0]]
  ![![506, 24, -35]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00
 hI2 := rfl
 M := ![![![125, 0, 0], ![-25, 25, 0]], ![![20, 5, 0], ![-6, 1, 10]]]
 hmul := by decide
 f := ![![![![-106881914732238891, -12020680962540419, -747801714668815], ![18972246753939695, 0, 3739011997038240]], ![![10161920178480, 0, -2860706880], ![22978024, 0, -8000]]]]
 g := ![![![![-66052, -8369, -6635]], ![![-179838, -22786, -18065]]], ![![![-49178, -6231, -4940]], ![![-133896, -16965, -13450]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow3 : J0 ^ 3 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ01, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![13300589690194, 1685223718337, 1336060678437])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![5, 0, 0], ![-1, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl

lemma PowJ0_2 : J0 ^ 2 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![25, 0, 0], ![4, 1, 0]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 simp only [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00]
 rfl     
