import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_15187500000_9.RI5_1_15187500000_9

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![1530364524268211603925253398141860677051, -675677904481168252931768110431333037888, 373095243342993183877459861246567961030, 211552063237507656708641407949570313766, 179931034736764358496291078720735012892]

def zeta2 := B.equivFun.symm ![15700996044218037685738004591007376553001, -33122543361251024510364321905370969500717, 2562229048361152066791072093801268605470, 3635085186266822471103424343712833368184, 4411991689003335472831892416865354529658]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-103806309065111349, 92685012578184588, -58793029706260170, -8141145852283226, 18559436679513068])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![143129479268299160393946750401, -63194631559428069910841776153, 34894685071796850921900093240, 19785991779555637255900756556, 16827227567168117747290907342])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

