import IdealArithmetic.Examples.NF3_1_297332_1.PrimesBelow3_1_297332_1F3
import IdealArithmetic.Examples.NF3_1_297332_1.ClassGroupData3_1_297332_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 20 ![![139, 0, 0], ![17, 1, 0]]
  ![-2099, -687, -137] ![![20, 0, 0], ![-18, -2, 1]] where
    su := ![![2780, 0, 0], ![340, 20, 0]]
    hsu := by decide
    w := ![![-41980, -13740, -2740], ![-25820, -8440, -1680]]
    hw := by decide
    g := ![![![-570590260, -62649684, 980492], ![519845251, 134863766, 0]], ![![-72676164, -7979699, 124885], ![66212777, 17177619, 0]]]
    h := ![![![-592124, -35447, -73], ![4841361, 5005, 0]], ![![-364202, -21812, -46], ![2977811, 3155, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {20} * I139N1 =  Ideal.span {B.equivFun.symm ![-2099, -687, -137]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 2 ![![149, 0, 0], ![-67, 1, 0]]
  ![81, 7, -3] ![![2, 0, 0], ![-22, -2, 1]] where
    su := ![![298, 0, 0], ![-134, 2, 0]]
    hsu := by decide
    w := ![![162, 14, -6], ![220, -92, 14]]
    hw := by decide
    g := ![![![337, -170, 666], ![-3107, -447, 0]], ![![-135, 81, -304], ![1419, 204, 0]]]
    h := ![![![11181, -134, -1], ![24864, 73, 0]], ![![15194, -259, 1], ![33788, -71, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {2} * I149N1 =  Ideal.span {B.equivFun.symm ![81, 7, -3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E149RS1 
