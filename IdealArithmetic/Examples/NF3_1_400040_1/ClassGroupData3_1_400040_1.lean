import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_400040_1.RI3_1_400040_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-12546433838102533649147562717060878378573863717050664550121869849649312026612102983, -1429171537147859019788492863939289178032614952873285423566472952423577936018204458, -1357490781559801491182937971062673178151814805281795079462046938694780441527196192]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![149478072933632965597663565394681774842969, 7476854221660700277484234115371391958446, -14015949122730102350305222012114669864392])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

