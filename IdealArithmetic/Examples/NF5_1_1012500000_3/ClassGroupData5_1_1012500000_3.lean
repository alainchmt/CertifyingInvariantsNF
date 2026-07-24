import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_1012500000_3.RI5_1_1012500000_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-31715, -289, 2087, 3977, 1486]

def zeta2 := B.equivFun.symm ![-381783836090487737914127461786618, -538841837038128908337298161150068, -104206442251627127723905800740217, -51617800043183880169188951328416, 171368105353606895650848692747406]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1367565, 2504931, 1152573, -46183, -1007068])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-393807610161700547429470545687742030507783852, -381878831483388810841544982370881526534136804, -376345047931557293193690605271875618177899583, -283238369622647669287252302092154592790937078, -229541493981824426020300317813822836452619184])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

