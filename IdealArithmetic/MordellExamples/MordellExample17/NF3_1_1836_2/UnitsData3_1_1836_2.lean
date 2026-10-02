import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.MordellExamples.MordellExample17.NF3_1_1836_2.RI3_1_1836_2

namespace NF3_1_1836_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![7, 1, 1]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1, -1, 0])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma v_pow_one : v ^ 2 = 1 := by
  rw [← B_one_repr]
  apply table_nPow_sq_table_eq_pow timesTableO.table Table B _ (timesTableO.basis_mul_basis) 
   timesTableT_eq_Table _ (by norm_num)
  decide

end

end NF3_1_1836_2
