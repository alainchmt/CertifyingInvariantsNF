import IdealArithmetic.Examples.NF3_3_157300_2.PrimesBelow3_3_157300_2F2
import IdealArithmetic.Examples.NF3_3_157300_2.ClassGroupData3_3_157300_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 3 ![![83, 0, 0], ![16, 1, 0]]
  ![-19, -26, 9] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![249, 0, 0], ![48, 3, 0]]
    hsu := by decide
    w := ![![-57, -78, 27], ![117, 171, -60]]
    hw := by decide
    g := ![![![716, 1119, 113], ![615, 0, -166]], ![![133, 208, 21], ![117, 0, -31]]]
    h := ![![![123, 2254, 423], ![92, -11700, 0]], ![![-282, -4611, -865], ![-30, 23925, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {3} * I83N1 =  Ideal.span {B.equivFun.symm ![-19, -26, 9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS1 
