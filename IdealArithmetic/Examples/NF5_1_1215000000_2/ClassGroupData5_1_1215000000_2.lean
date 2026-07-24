import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_1215000000_2.RI5_1_1215000000_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![20262966943, -8406203686, 16178162060, -10469966454, 64987099008]

def zeta2 := B.equivFun.symm ![61725567150698132, -23732412184790670, 53877396440796574, -34593497573756850, 221463026414514967]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-54419734978461981777007555821245, 9896347120341782846805956331286, -17589121081587873030235023918120, 6348932749491592905132199646474, -46467305004421896437039650003068])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![14981650995254522273548326, -4580128292228907931773770, -6629120815288083195465974, 1667112721632006788118140, -16814962804167594838571047])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

