import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF3_1_931736_1.RI3_1_931736_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0]

def zeta1 := B.equivFun.symm ![-27483847745552591479157409997372664977817915677838502079356650875337917650850919088975, -8349618571098992436533541306511859547922194511953166908731951275815334599706353918972, -1371488498369572677461614295312312766175300443855068824976505652504897812796585615451]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![11926804047424523713601845636882308831958347, 1761928921322497468581777676621864316658778, -490598493321372379641682077844988877281223])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

