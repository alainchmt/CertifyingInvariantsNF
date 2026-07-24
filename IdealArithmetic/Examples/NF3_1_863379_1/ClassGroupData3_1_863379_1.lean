import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_863379_1.RI3_1_863379_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-62682261655876266170501047325497393151, 32793850120283888188187277560344129098, 3301578834175564918936169809917133104]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![106069674002829756022942024035942021209381881242354410919079092451640146365049, 3069332014182899706650052459591392455033320779259798520231745930294503765686, 1871009865179847715510154177683480006766407822441899280384510167012019704372])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

