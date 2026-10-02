import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.MordellExamples.MordellExample17.NF2_2_17_1.RI2_2_17_1

namespace NF2_2_17_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0]

def zeta1 := B.equivFun.symm ![5, -2]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-3, -2])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide


lemma PowUnit : (1 : Ideal O) = Ideal.span (Set.range fun i ↦ B.equivFun.symm (![![1, 0]] i)) := by
 simp only [Set.range_unique, Matrix.cons_val_fin_one]
 rw [B_one_repr, Ideal.span_singleton_one, Ideal.one_eq_top]

end

end NF2_2_17_1
