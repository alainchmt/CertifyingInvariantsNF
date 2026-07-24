import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_1822500000_1.RI5_1_1822500000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-1210667915, 60429106, -95894947, 326035082, 228334455]

def zeta2 := B.equivFun.symm ![-8671266421007374585883789350749374548214231, -3332033242391008513161151935166669221962082, -1957474963529016027306750680070737951608823, -1139252032909478872903270391669130156036502, -1283144438351372337764457553975345277480767]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![36439216664731, -6176989778160, -51545816229, -2547071141704, -2296380610001])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![499371540712128780338719, -171933756830858721846788, -7628684343108375158077, -177073886179678500032008, 126381350164183205540657])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

