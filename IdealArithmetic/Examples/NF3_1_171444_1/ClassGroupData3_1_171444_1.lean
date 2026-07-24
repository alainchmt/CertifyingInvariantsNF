import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_171444_1.RI3_1_171444_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![329979241032467417088767099741890030357283053, 40187511159751057681025712029673081367836991, -62131775560666791520421879965571795253759183]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-363683291065551401900053219762262864092022854487560248698638869019741247321694435106645923, -35308567461480341294930712816390543656590576201177600476674417316979044156348468340009753, -32919284684002383363957521348826719981136029462044049988119388089718229876729065603608457])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

