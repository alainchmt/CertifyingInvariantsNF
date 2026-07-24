import IdealArithmetic.Examples.NF3_1_623807_1.PrimesBelow3_1_623807_1F3
import IdealArithmetic.Examples.NF3_1_623807_1.ClassGroupData3_1_623807_1

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 4 ![![149, 0, 0], ![-2, 1, 0]]
  ![-164, 4, 7] ![![4, 0, 0], ![-1, 0, 1]] where
    su := ![![596, 0, 0], ![-8, 4, 0]]
    hsu := by decide
    w := ![![-656, 16, 28], ![-292, 528, -168]]
    hw := by decide
    g := ![![![-1493, -273, -154], ![335, 0, 0]], ![![-11, -9, -4], ![6, -1, 0]]]
    h := ![![![0, -82, 163], ![82, -12140, 0]], ![![1, -37, 74], ![111, -5534, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {4} * I149N1 =  Ideal.span {B.equivFun.symm ![-164, 4, 7]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E149RS1 


noncomputable def E191RS1 : RelationCertificate Table 2 ![![191, 0, 0], ![-15, 1, 0]]
  ![-26, -4, -1] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![382, 0, 0], ![-30, 2, 0]]
    hsu := by decide
    w := ![![-52, -8, -2], ![-482, -80, -24]]
    hw := by decide
    g := ![![![-33, 4, 7], ![-13, 0, 0]], ![![-188, -2, 38], ![-73, 3, 0]]]
    h := ![![![-106, 14, -1], ![-1348, 95, 0]], ![![-1046, 83, -2], ![-13303, 185, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {2} * I191N1 =  Ideal.span {B.equivFun.symm ![-26, -4, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E191RS1 
