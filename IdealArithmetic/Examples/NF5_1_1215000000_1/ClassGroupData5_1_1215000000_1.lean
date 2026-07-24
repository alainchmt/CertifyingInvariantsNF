import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_1215000000_1.RI5_1_1215000000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-1776948664, 764018012, 30534239, 103732003, -299128803]

def zeta2 := B.equivFun.symm ![-1657401436993832853487, 1248118646468693117498, -1918743789354661239658, 943875027253156154220, -581642806879983185016]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![241137569303623211576914578464, -119493288437405481481807242562, 53334603698212597388361734327, -7974359637489125134198872765, 88915325308660875359674274061])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![76422584623341117278423441, -48646653649358228745855598, 579114033742256183687462, -5220095084980775615646368, 19327485255456935489855448])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

