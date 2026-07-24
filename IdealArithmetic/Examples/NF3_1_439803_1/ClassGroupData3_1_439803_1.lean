import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_439803_1.RI3_1_439803_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![21542331426626560709808586634775808142304099, -6317248662490541733961770108907944671799052, 218165878872644682909455125205944724372438]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-7000148793988895405833723604251571239787783559564775329684545334424007328078613303919621, -96513808182975980261341835924087774125226927929754896475052238270867843352699074262352, -312804350793023697165992109413469492647930333769801195785974189535409745926888343449442])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

