import IdealArithmetic.Examples.NF3_3_333617_1.PrimesBelow3_3_333617_1F1
import IdealArithmetic.Examples.NF3_3_333617_1.ClassGroupData3_3_333617_1

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 3 ![![41, 0, 0], ![-17, 1, 0]]
  ![-1, -22, 3] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![123, 0, 0], ![-51, 3, 0]]
    hsu := by decide
    w := ![![-3, -66, 9], ![-1344, -327, 69]]
    hw := by decide
    g := ![![![16, 153, 26], ![-14, 0, 0]], ![![24, -35, -7], ![6, 0, 0]]]
    h := ![![![-22, 2, 0], ![-53, 3, 0]], ![![-24782, 1634, -10], ![-59742, 433, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {3} * I41N0 =  Ideal.span {B.equivFun.symm ![-1, -22, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS0 


noncomputable def E47RS1 : RelationCertificate Table 3 ![![47, 0, 0], ![-2, 1, 0]]
  ![-2, 1, 0] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![141, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![-6, 3, 0], ![117, 18, -3]]
    hw := by decide
    g := ![![![27, 2, -1], ![4, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-10, 7, -1], ![-234, 47, 0]], ![![205, -102, 0], ![4798, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {3} * I47N1 =  Ideal.span {B.equivFun.symm ![-2, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E61RS1 : RelationCertificate Table 3 ![![61, 0, 0], ![26, 1, 0]]
  ![-84, 4, 1] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![183, 0, 0], ![78, 3, 0]]
    hsu := by decide
    w := ![![-252, 12, 3], ![2769, 156, -72]]
    hw := by decide
    g := ![![![33, -125, -23], ![16, 0, 0]], ![![31, -68, -13], ![10, 0, 0]]]
    h := ![![![-2280, -140, -2], ![5346, 123, 0]], ![![25051, 1364, 15], ![-58738, -939, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {3} * I61N1 =  Ideal.span {B.equivFun.symm ![-84, 4, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E79RS0 : RelationCertificate Table 3 ![![79, 0, 0], ![11, 1, 0]]
  ![18, 5, -1] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![237, 0, 0], ![33, 3, 0]]
    hsu := by decide
    w := ![![54, 15, -3], ![-228, 54, -3]]
    hw := by decide
    g := ![![![30, 12, 1], ![1, 0, 0]], ![![14, 3, 0], ![1, 0, 0]]]
    h := ![![![64, 6, 0], ![-458, -1, 0]], ![![-346, -42, -1], ![2478, 78, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {3} * I79N0 =  Ideal.span {B.equivFun.symm ![18, 5, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS0 
