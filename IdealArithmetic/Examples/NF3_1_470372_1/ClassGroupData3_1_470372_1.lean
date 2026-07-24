import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_470372_1.RI3_1_470372_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-11125332349750751537215601659462315254493905, 1585581771176375921003715239608082068150365, 945196953189472502156461732229895607896812]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![826606078690424840285469717953780183022690891012630852826738823792529470290070069180377, 33677138143529843756293441447197590740470796825778666095197728932344287735249951842211, 43955934019576696926891158889243382866302161819004836218810986026728261428741174931094])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

