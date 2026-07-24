import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_15187500000_13.RI5_1_15187500000_13

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![28233265426081834369, 18707994442679120572, 34653191065394154206, 25697915106684346830, -96048529667647541898]

def zeta2 := B.equivFun.symm ![4978784906099655323369580196932693671209, 577130883306450963012509285197673544040, -772589251818782954496455580447404187409, -613128935409891373010738918365415117857, 1700063098902632256066373308172240171233]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![2673169854667049825, 309868516734379324, -414812500049361902, -329196329204349582, 912784411170616362])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![250981211812898071269390727854795534016651377661, 811782809240712993003642883186857503063644616514, -491307620824436354432488829711560936983710260505, -642623824603641964699468813420682839228452322981, 1359969396833190741634230902318145028395885011213])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

