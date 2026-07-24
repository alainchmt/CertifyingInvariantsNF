import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_946067_1.RI3_1_946067_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-18841429279167160642131744559056, 856715630841343257321641602926, 180103433790937688697780539233]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![73511339446186695096795348149478717433958201118720509515185718, 22986006059007737954103295441421953031265464546038060129566835, 2829877908303531249622814929305689176471639518658066056073964])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

