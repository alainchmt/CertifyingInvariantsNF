import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_5695312500_2.RI5_1_5695312500_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-668659409462317, -9788069568220357, 3303784937823971, 796039613263702, 41116211294214996]

def zeta2 := B.equivFun.symm ![-262374041549, -61044783805, -76022460672, 20640388795, -177015755340]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-6844119015189484858209633, -975853707146478691027246, -114295105565829530634671, 182791099983225472579041, 355842893338247340689768])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![1042047377002406093834703708750203, 1241828799834698220178619613543383, 893142121803943403281355791546122, 283416053620856999780721904322737, 550364359339688963557875561666476])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

