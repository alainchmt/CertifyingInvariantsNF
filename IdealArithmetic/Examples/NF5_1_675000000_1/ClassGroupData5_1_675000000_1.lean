import IdealArithmetic.IdealArithmetic.IdealArithmetic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import IdealArithmetic.Examples.NF5_1_675000000_1.RI5_1_675000000_1

set_option linter.all false

open BigOperators Classical Matrix Polynomial Module
noncomputable section

def v := B.equivFun.symm ![-1, 0, 0, 0, 0]

def zeta1 := B.equivFun.symm ![115, 103, 48, -19, -26]

def zeta2 := B.equivFun.symm ![187152978464204181187458526443796307757503998609279230881977578942853773, 255994914730260386947067216717549612198842283681127221307073195118177141, 206505920634577250135895550361632809825029976942412100283891321153724922, 95620445449377997763081636787086536285401376358221083838865163055929473, 66887314133408457399065536875003329100058654279841172019672039116923172]

lemma isUnit_zeta1 : IsUnit zeta1 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-32661, -16315, -2902, -1527, 3832])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

lemma isUnit_zeta2 : IsUnit zeta2 := by 
 apply IsUnit.of_mul_eq_one (B.equivFun.symm ![-115428317300900918294963833190767829146924214903177931, -106066415276354057093513781906431055240333265102647701, -53040648880300445742499224304954978055249419688364332, 11737441410663345544228222256629519760888843183255557, 17118854574531897983760122376112043403982306262696758])
 rw [← B_one_repr]
 refine table_mul_list_eq_mul timesTableO.table B _ _ _ timesTableO.basis_mul_basis ?_
 rw [← table_mul_eq_table_mul' _ _ timesTableT_eq_Table]
 decide

