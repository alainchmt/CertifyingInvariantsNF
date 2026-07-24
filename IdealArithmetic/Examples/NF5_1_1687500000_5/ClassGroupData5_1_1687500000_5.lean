import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_1687500000_5.RI5_1_1687500000_5

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-1140481, -1179400, -359087, -13693, 30552]

def zeta2 := B.equivFun.symm ![-4386529219156690034524930755616427855190051239, -9343744830686218930640566025618986407532790890, -5893240390389063477619231770417694849840061157, -859559682394146286741328661636777594230986931, 611763855286582307976867116311287048267404408]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-69600080961, -141015678880, -114063807987, -38113352827, -11516710560])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![2044133501965362916731438726227227295401, 3256330543826369470383422420287597820610, 1152400264038201896834303322084059060943, 96746417663205851791056855770605453731, -108921987701202135597622133255228330296])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

