import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_18225000000_1.RI5_1_18225000000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![-618327545750792164607138015, 504358031073360083089315273, -108578980249994756945750546, 122266746529802383009555546, -178659993337591354861863450]

def zeta2 := B.equivFun.symm ![-196497252156153834437249257270996293799044811845550550944616908198171, -6503470046930124112228164315665144763465582450985189868244896930233, -12821698366595669227869882316801000169611275658565184549361529125596, -2203424909399112098161523605075088166634577159312568715912048801296, -12013422216134581344147706588947801557789783529344879220231296194172]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-496821619172134176311, 281411445542132698101, -17427684194891548368, 46149093726218932702, -62149774502725740546])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-1040633131239988999590755347, 401632619565852795565152619, 42518437709130440477774610, 111046331343706791610258548, 68006999771938038261248348])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

