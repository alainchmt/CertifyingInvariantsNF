import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_628963_1.RI3_1_628963_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![6771134477578949026013028478688909905064519, -310076584155882208283728562181272188439682, -412501905564090819902870481874869647405220]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-69465417081852218304600861967153704548701744498256703987536219383227378237442702111465, -7651258991183354467471271632830909139688687219334345607843831221761434583559237682326, -3783161520264544842587090891781987161227097099511158923646312786852283266039970425040])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

