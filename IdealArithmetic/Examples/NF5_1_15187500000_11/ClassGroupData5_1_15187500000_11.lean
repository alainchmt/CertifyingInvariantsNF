import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_15187500000_11.RI5_1_15187500000_11

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-47777123285, -1207296009034, -737028603351, -724523175575, 2701848127854]

def zeta2 := B.equivFun.symm ![1614839924445089970413220160604005103, -1482104006082511044499945419227501423, 157369673619449790035573035092056326, 361689481213134025339966901903975995, -1572682920502802123581506121533435062]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-318988660682441441, 137967155574065630, 107624425957479707, 115064873444033265, -430190474868036310])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![487403894413743740802537775281743374567336227905, -440527024220755751724664006156990159559818425701, 416486896394580759819126667922667236468898231960, 212733549666337449083456118688087387778852501535, -859461379405497210542631063046179517361982118524])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

