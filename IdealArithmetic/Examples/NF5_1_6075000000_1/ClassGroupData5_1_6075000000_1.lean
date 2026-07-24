import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_6075000000_1.RI5_1_6075000000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-26048301597828188719052509, -46761400315146136826184103, 28965152108610461104879949, -14450713414333789671728068, 27536252760824478370084144]

def zeta2 := B.equivFun.symm ![613237075772627, 41847309765258055, 15354078185624865, 16432556522138966, 44099063420918446]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![16774522164001161924880787, -197759257687552566887038187, -142293169122584411251480029, -165716741316850817989223872, -179065254079874415997765604])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-21022816917550599682014278815255170290007936997, 1141350443671658440069579692402686434477185767, -2893656206373791138507409004377392036733960361, -2024643037780885455912228608398801013332328554, -5048290686199485547670173320413797654233716042])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

