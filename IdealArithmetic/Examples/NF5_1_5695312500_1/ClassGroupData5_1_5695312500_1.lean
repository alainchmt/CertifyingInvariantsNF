import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_5695312500_1.RI5_1_5695312500_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-17445366704677495937285158, 13335018056357342124887029, -6965963626285607787072618, -2102891807246656508182313, -25911864791245683551718968]

def zeta2 := B.equivFun.symm ![-3684371939167887037526686, 2816282136943990077717586, -1471172618713130313427329, -444118989095766526922833, -5472441613773577693122950]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-56446306780183739853218951806, -75693592560789968353255098504, 49457175400081984414851490561, 15322645204627002042128086177, 172910771730052428147158653220])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-112730778129758367607365529438, -110134513512494528675549796411, 107848916333180438303561313562, 15406878012104504728423094817, 307650030971364585563408407562])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

