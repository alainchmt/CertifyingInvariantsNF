import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_121500000_2.RI5_1_121500000_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-523558, 498668, -50021, -257907, -417756]

def zeta2 := B.equivFun.symm ![24440867431, 23711652752, 28782713998, 59733122646, 47679568190]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-3174904, -19764662, -1039361, -4310079, -18998214])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-989802997890438658758197, 117460367547080424294076, -65146788707626010441002, -146359633852253936541678, -255011387119649674857658])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

