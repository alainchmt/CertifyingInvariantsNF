import IdealArithmetic.Examples.NF3_1_105791_3.PrimesBelow3_1_105791_3F2
import IdealArithmetic.Examples.NF3_1_105791_3.ClassGroupData3_1_105791_3

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 9 ![![83, 0, 0], ![-17, 1, 0]]
  ![9, 2, 1] ![![9, 0, 0], ![4, -3, -1]] where
    su := ![![747, 0, 0], ![-153, 9, 0]]
    hsu := by decide
    w := ![![81, 18, 9], ![-279, -117, -18]]
    hw := by decide
    g := ![![![2985230, 537562, 289693], ![1115401, 497280, 0]], ![![-591670, -106542, -57416], ![-221065, -98560, 0]]]
    h := ![![![1551, -91, 0], ![7572, 1, 0]], ![![-5297, 328, -1], ![-25860, 81, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {9} * I83N1 =  Ideal.span {B.equivFun.symm ![9, 2, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 9 ![![89, 0, 0], ![31, 1, 0]]
  ![-36, 4, 1] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![801, 0, 0], ![279, 9, 0]]
    hsu := by decide
    w := ![![-324, 36, 9], ![207, -45, 0]]
    hw := by decide
    g := ![![![-161079, 40148, 32], ![-362441, -283, 0]], ![![-57998, 14458, 11], ![-130501, -97, 0]]]
    h := ![![![-270, -40, -1], ![774, 90, 0]], ![![126, 4, 0], ![-361, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {9} * I89N1 =  Ideal.span {B.equivFun.symm ![-36, 4, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E89RS1 
