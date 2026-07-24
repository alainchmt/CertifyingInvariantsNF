import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_3037500000_1.RI5_1_3037500000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-570952446171307683, 305282645773297475, 240772938860071459, -585229628347126528, -1251621586609204502]

def zeta2 := B.equivFun.symm ![-130954264944862880599556951951, 643216518869864848297260841686, 897474027604923622808021048718, -2439791929197826607668314938918, -5382424375399144929695244006654]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![69387174796203576899922093584855, -4152303658349936770515564326165, -13606228336958551619917926339649, 42794280592027363599410527790008, 89658923732777124873898079582432])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-6556959375398383119721884584151, 392384997401685370379559210314, 1285763352087262539840747682522, -4043980175954296959747611318782, -8472602066368137625307688203886])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

