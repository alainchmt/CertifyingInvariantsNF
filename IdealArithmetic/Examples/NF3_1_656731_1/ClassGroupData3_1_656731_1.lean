import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_656731_1.RI3_1_656731_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def alpha0 := B.equivFun.symm ![-657854, 197055, -24817]

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![11275628885822324136574273, -4225687235324269362059919, 2803895064219778144032788]

def J0 : Ideal O := Ideal.span (Set.range (fun i ↦ B.equivFun.symm (![![2, 0, 0], ![16, 1, 1]] i)))
def MulJ00 : IdealMulEqCertificate timesTableO (J0) J0
  ![![2, 0, 0], ![16, 1, 1]] ![![2, 0, 0], ![16, 1, 1]]
  ![![-657854, 197055, -24817]] where
 T := Table
 heq := timesTableT_eq_Table
 hI1 := rfl
 hI2 := rfl
 M := ![![![4, 0, 0], ![32, 2, 2]], ![![32, 2, 2], ![438, -9, 19]]]
 hmul := by decide
 f := ![![![![-2330231, 8887443, 1924508], ![-13235844, 0, 0]], ![![0, 0, 0], ![986781, 0, 0]]]]
 g := ![![![![-2141361277857, -23778482842, -85760246077]], ![![-22207875033523, -246604615906, -889412191869]]], ![![![-22207875033523, -246604615906, -889412191869]], ![![-230315976385891, -2557515422251, -9224017924750]]]]
 hle1 := by decide
 hle2 := by decide

lemma J0_pow2 : J0 ^ 2 = Ideal.span {alpha0} := by
 simp only [pow_succ, pow_one, pow_zero, one_mul]
 simp [ideal_eq_mul_of_IdealMulEqCertificate timesTableO _ _ _ _ _ MulJ00, alpha0]
 rfl
lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-7638757351955738739276983522287203927417319287329838, -84823641160382778152101497290979732728460406947934, -305927690483793604538920587775360021543658107962409])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

lemma PowJ0_1 : J0 ^ 1 = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![2, 0, 0], ![16, 1, 1]] i)) := by 
 simp only [pow_succ, pow_one, pow_zero, one_mul, mul_one]
 rfl
