import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_3645000000_4.RI5_1_3645000000_4

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-35709978791, -5849628480, -64020826591, -70239238610, 181848706997]

def zeta2 := B.equivFun.symm ![-1591794520292955979570801171, 551001074982761201342576569, 479914974099161536013332759, 353377596985756641016484700, -1095357951548117118029163554]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-36145975951793378777943, 12511959761532190198176, 10897743250579090566835, 8024372500394068344536, -24873004500926703336599])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-662132902835743081237811445300924611, 559180707117416458382169303122569725, 506642927316052619400449639882060239, 376505822094865777433995858199927774, -1197452105850662865362721400664914062])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

