import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_2025000000_8.RI5_1_2025000000_8

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-2860188783391431361, 4686373319349692104, 3132887392012610645, 2085875724792895371, -10286974511398607442]

def zeta2 := B.equivFun.symm ![-35794142406490183957, -35426857278067159667, -18861533340686846387, -14063374944833369166, 82766156452614767892]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-2576198073695259829, -2042311294473984956, -814028840160074937, -380728446605947297, 1983851796229122594])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-470672281374655182234791276791, 148332597767715287312322262367, 153196607510015991098264466377, 62519298964537302502286654866, -351079681318920585855951808422])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

