import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_679112_1.RI3_1_679112_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-334528000027092746980377311240583373694435591264627773720987260432417466770292863015089333889, 62981423025325980536859808498767567892231659545218875645021454508400471144411453858528491177, -10537449103320619860064906750625741805844119157862265054388185830274692338696977396745456091]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-2918624379864129937338175601391870934003242331, -3145203232566493756479698095594094172471116171, -514127998258386056429116854215317329762668885])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

