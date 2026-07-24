import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_1687500000_2.RI5_1_1687500000_2

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-61862919999, -105945431485, 33702817010, 9576232575, 81497412275]

def zeta2 := B.equivFun.symm ![6306959519433058014797539, 569991405011014850807629, -21661361430752199137953, -393805859897876397247110, 40428228178163716576680]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![47063261550772341001, 48622046730127622985, 70485620627916949340, 55134007433855782925, 49897706847337446725])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![2001123099960831612920118372619, 1026074360573854466819456487831, -125931302544051404433252091013, -361597962642042842898331121240, -318435630994542773942589007440])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

