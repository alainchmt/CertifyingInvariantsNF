import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_782987_1.RI3_1_782987_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![377459298580750070734701161731, 210030877048037332246788258984, 20525748990471867474114357414]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![2982849594717016723106924654065892197935353480828016151931251, -195532443737753337414909774363089217599828569615500546511692, 58792549538970244403740418681518602358096870237336357294026])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

