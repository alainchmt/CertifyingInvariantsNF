import IdealArithmetic.Examples.NF3_3_262601_1.PrimesBelow3_3_262601_1F2
import IdealArithmetic.Examples.NF3_3_262601_1.ClassGroupData3_3_262601_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![44, 1, 0]]
  ![9, 4, -1] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![178, 0, 0], ![88, 2, 0]]
    hsu := by decide
    w := ![![18, 8, -2], ![626, 76, -28]]
    hw := by decide
    g := ![![![2, 12, 3], ![-1, 0, 0]], ![![27, 9, 1], ![1, 0, 0]]]
    h := ![![![713, -6, -1], ![-1442, 44, 0]], ![![26977, 707, 4], ![-54560, -185, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![9, 4, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E113RS0 : RelationCertificate Table 2 ![![113, 0, 0], ![19, 1, 0]]
  ![-1, 4, 1] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![226, 0, 0], ![38, 2, 0]]
    hsu := by decide
    w := ![![-2, 8, 2], ![158, 4, -4]]
    hw := by decide
    g := ![![![18, -16, 3], ![13, 0, 0]], ![![11, -1, 0], ![2, 0, 0]]]
    h := ![![![1, -30, -3], ![-6, 170, 0]], ![![73, -16, -2], ![-430, 112, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {2} * I113N0 =  Ideal.span {B.equivFun.symm ![-1, 4, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E113RS0 


noncomputable def E113RS2 : RelationCertificate Table 2 ![![113, 0, 0], ![51, 1, 0]]
  ![-121, -22, 7] ![![2, 0, 0], ![-30, -2, 1]] where
    su := ![![226, 0, 0], ![102, 2, 0]]
    hsu := by decide
    w := ![![-242, -44, 14], ![-1874, -344, 108]]
    hw := by decide
    g := ![![![12, 26, -5], ![43, 0, 0]], ![![3, 11, -2], ![18, 0, 0]]]
    h := ![![![-9140, -259, -3], ![20249, 173, 0]], ![![-70850, -1715, -12], ![156963, 705, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {2} * I113N2 =  Ideal.span {B.equivFun.symm ![-121, -22, 7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E113RS2 
