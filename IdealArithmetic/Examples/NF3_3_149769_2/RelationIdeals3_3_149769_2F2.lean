import IdealArithmetic.Examples.NF3_3_149769_2.PrimesBelow3_3_149769_2F2
import IdealArithmetic.Examples.NF3_3_149769_2.ClassGroupData3_3_149769_2

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 169 ![![83, 0, 0], ![13, 1, 0]]
  ![-455, -53, 5] ![![169, 0, 0], ![-57, 1, 0]] where
    su := ![![14027, 0, 0], ![2197, 169, 0]]
    hsu := by decide
    w := ![![-76895, -8957, 845], ![28730, 3211, -338]]
    hw := by decide
    g := ![![![214, 102536, -1799], ![616, 304020, 0]], ![![40, 17156, -301], ![117, 50868, 0]]]
    h := ![![![-2041, -171, -1], ![12996, 88, 0]], ![![736, 57, 0], ![-4686, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {169} * I83N0 =  Ideal.span {B.equivFun.symm ![-455, -53, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 169 ![![83, 0, 0], ![-8, 1, 0]]
  ![1287, 102, -16] ![![169, 0, 0], ![-57, 1, 0]] where
    su := ![![14027, 0, 0], ![-1352, 169, 0]]
    hsu := by decide
    w := ![![217503, 17238, -2704], ![-82303, -6591, 1014]]
    hw := by decide
    g := ![![![-2903895, -1620606403, 28432585], ![-8609812, -4805106877, 0]], ![![40161, 22386274, -392754], ![119077, 66375428, 0]]]
    h := ![![![1859725, -234456, 249], ![19294486, -20683, 0]], ![![-703709, 88723, -95], ![-7300920, 7891, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {169} * I83N1 =  Ideal.span {B.equivFun.symm ![1287, 102, -16]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 169 ![![83, 0, 0], ![-5, 1, 0]]
  ![-1742, -155, 21] ![![169, 0, 0], ![-57, 1, 0]] where
    su := ![![14027, 0, 0], ![-845, 169, 0]]
    hsu := by decide
    w := ![![-294398, -26195, 3549], ![111033, 9802, -1352]]
    hw := by decide
    g := ![![![136, 53926, -946], ![439, 159896, 0]], ![![7, -2110, 37], ![16, -6256, 0]]]
    h := ![![![-1538434, 308747, -213], ![-25537656, 17700, 0]], ![![580229, -116439, 79], ![9631670, -6565, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {169} * I83N2 =  Ideal.span {B.equivFun.symm ![-1742, -155, 21]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS2 
