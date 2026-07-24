import IdealArithmetic.Examples.NF3_1_325983_1.PrimesBelow3_1_325983_1F3
import IdealArithmetic.Examples.NF3_1_325983_1.ClassGroupData3_1_325983_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 9 ![![139, 0, 0], ![32, 1, 0]]
  ![25, -6, 2] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![1251, 0, 0], ![288, 9, 0]]
    hsu := by decide
    w := ![![225, -54, 18], ![135, 9, -36]]
    hw := by decide
    g := ![![![76, 931, -2342], ![87, 4220, 0]], ![![20, 217, -546], ![22, 984, 0]]]
    h := ![![![6955, 204, -2], ![-30210, 56, 0]], ![![4173, 124, -1], ![-18126, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {9} * I139N1 =  Ideal.span {B.equivFun.symm ![25, -6, 2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E139RS1 


noncomputable def E151RS1 : RelationCertificate Table 27 ![![151, 0, 0], ![8, 1, 0]]
  ![103, 3, 5] ![![27, 0, 0], ![-3, 1, 0]] where
    su := ![![4077, 0, 0], ![216, 27, 0]]
    hsu := by decide
    w := ![![2781, 81, 135], ![216, 27, 0]]
    hw := by decide
    g := ![![![1, -344, 860], ![6, -4645, 0]], ![![0, -20, 50], ![1, -270, 0]]]
    h := ![![![-231, -29, 0], ![4373, 1, 0]], ![![-24, -3, 0], ![454, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {27} * I151N1 =  Ideal.span {B.equivFun.symm ![103, 3, 5]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E151RS1 
