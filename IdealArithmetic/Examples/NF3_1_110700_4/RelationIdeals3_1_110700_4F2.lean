import IdealArithmetic.Examples.NF3_1_110700_4.PrimesBelow3_1_110700_4F2
import IdealArithmetic.Examples.NF3_1_110700_4.ClassGroupData3_1_110700_4

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 169 ![![83, 0, 0], ![-14, 1, 0]]
  ![87, -25, 6] ![![169, 0, 0], ![-24, 1, 0]] where
    su := ![![14027, 0, 0], ![-2366, 169, 0]]
    hsu := by decide
    w := ![![14703, -4225, 1014], ![-2028, 507, -169]]
    hw := by decide
    g := ![![![108003, 131110933, -5463143], ![760514, 923271174, 0]], ![![-18628, -22641640, 943434], ![-131171, -159440347, 0]]]
    h := ![![![137, -9, 0], ![806, 6, 0]], ![![12, 13, -1], ![72, 82, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {169} * I83N1 =  Ideal.span {B.equivFun.symm ![87, -25, 6]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E83RS1 
