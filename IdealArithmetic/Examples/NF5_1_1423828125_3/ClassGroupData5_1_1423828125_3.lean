import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_1423828125_3.RI5_1_1423828125_3

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-14105865261, -3935288090, 2086939514, 948262704, -3809142746]

def zeta2 := B.equivFun.symm ![-528869602422413756919274, 5762040367282942434975, 182294222305235048831735, -43284900635213227891439, -441473536727334550302414]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![7898927350915598515, 541084909133864810, -803841352918019162, 5540184871136439312, 11947088449894691502])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-27495578277168363973637180746, -1564864062600221750282137230, -2617188716558106143863373728, 2555410194233148433060299445, 8636433165787126548461192910])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

