import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_10125000000_12.RI5_1_10125000000_12

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![225130415712432254016341613951, 178281764794576850245284367025, 120951147481506850291004632055, 139405577529475737769210086790, 351495356316304913596765857925]

def zeta2 := B.equivFun.symm ![71934967246916774968782285065458035882544155280049, -12239361835048371443692951643018114738109919341395, 8497668134022491651002804137509717210020608499155, 9415796777509791356627752635063445185210098512360, 25494293777514841755556430844747086343913929043875]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![14509004151, 15895476325, 9816641045, 13263036210, 33127279225])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![999711484620916202512222634167905184702649, 1054545007482456334425056236166982758768345, 658103938904920385900447785670464433030645, 879447675024948619581637099018275694218140, 2211768588316282694844145061010951280496175])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

