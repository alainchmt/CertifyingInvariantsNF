import IdealArithmetic.Examples.NF3_3_806284_1.PrimesBelow3_3_806284_1F1
import IdealArithmetic.Examples.NF3_3_806284_1.ClassGroupData3_3_806284_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 2 ![![41, 0, 0], ![-18, 1, 0]]
  ![343, 4, -7] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![82, 0, 0], ![-36, 2, 0]]
    hsu := by decide
    w := ![![686, 8, -14], ![-9808, -104, 198]]
    hw := by decide
    g := ![![![31, -12, -4], ![3, 0, 0]], ![![21, 22, 0], ![-8, -3, 0]]]
    h := ![![![6887, -392, 1], ![15668, -24, 0]], ![![-98332, 5739, -31], ![-223706, 685, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![343, 4, -7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 2 ![![43, 0, 0], ![7, 1, 0]]
  ![13, 4, -1] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![86, 0, 0], ![14, 2, 0]]
    hsu := by decide
    w := ![![26, 8, -2], ![176, 76, -18]]
    hw := by decide
    g := ![![![18, 1, 0], ![-1, 0, 0]], ![![3, -19, 0], ![9, 3, 0]]]
    h := ![![![111, 12, -1], ![-680, 21, 0]], ![![830, 124, 1], ![-5086, -26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {2} * I43N1 =  Ideal.span {B.equivFun.symm ![13, 4, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![-20, 1, 0]]
  ![64, 43, 8] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![94, 0, 0], ![-40, 2, 0]]
    hsu := by decide
    w := ![![128, 86, 16], ![888, 558, 86]]
    hw := by decide
    g := ![![![-15706, 2974, 383], ![-6365, 0, 0]], ![![7381, -1398, -180], ![2992, 0, 0]]]
    h := ![![![12, 819, -86], ![25, 2025, 0]], ![![52, 5722, -601], ![100, 14145, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![64, 43, 8]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 2 ![![53, 0, 0], ![8, 1, 0]]
  ![8, 1, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![106, 0, 0], ![16, 2, 0]]
    hsu := by decide
    w := ![![16, 2, 0], ![8, 10, 2]]
    hw := by decide
    g := ![![![15, -1, -1], ![9, 0, 0]], ![![0, -1, 0], ![2, 0, 0]]]
    h := ![![![8, 1, 0], ![-52, 0, 0]], ![![4, -4, -1], ![-26, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {2} * I53N1 =  Ideal.span {B.equivFun.symm ![8, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E59RS0 : RelationCertificate Table 2 ![![59, 0, 0], ![26, 1, 0]]
  ![45, 20, -1] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![118, 0, 0], ![52, 2, 0]]
    hsu := by decide
    w := ![![90, 40, -2], ![736, 300, -34]]
    hw := by decide
    g := ![![![66, -187, 92], ![-601, 0, 0]], ![![35, -95, 37], ![-234, 3, 0]]]
    h := ![![![-131, -18, -1], ![299, 29, 0]], ![![-824, -12, 1], ![1884, -38, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {2} * I59N0 =  Ideal.span {B.equivFun.symm ![45, 20, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 2 ![![59, 0, 0], ![-16, 1, 0]]
  ![299, 8, -7] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![118, 0, 0], ![-32, 2, 0]]
    hsu := by decide
    w := ![![598, 16, -14], ![-7900, 4, 142]]
    hw := by decide
    g := ![![![38, -237, -54], ![25, 0, 0]], ![![14, 1, 4], ![8, 3, 0]]]
    h := ![![![33, 3335, -445], ![103, 13124, 0]], ![![-250, -44177, 5893], ![-675, -173808, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {2} * I59N1 =  Ideal.span {B.equivFun.symm ![299, 8, -7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 2 ![![59, 0, 0], ![-10, 1, 0]]
  ![-45, 0, 1] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![118, 0, 0], ![-20, 2, 0]]
    hsu := by decide
    w := ![![-90, 0, 2], ![1324, 20, -26]]
    hw := by decide
    g := ![![![0, 6, -1], ![-1, 0, 0]], ![![13, 18, 0], ![-8, -3, 0]]]
    h := ![![![-255, 30, -1], ![-1500, 30, 0]], ![![3838, -379, -1], ![22578, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {2} * I59N2 =  Ideal.span {B.equivFun.symm ![-45, 0, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS2 


noncomputable def E71RS0 : RelationCertificate Table 2 ![![71, 0, 0], ![4, 1, 0]]
  ![4, 1, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![142, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![8, 2, 0], ![4, 6, 2]]
    hw := by decide
    g := ![![![36, -6, -1], ![15, 0, 0]], ![![0, -1, 0], ![2, 0, 0]]]
    h := ![![![-4, -1, 0], ![72, 0, 0]], ![![-2, -3, -1], ![36, 36, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {2} * I71N0 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 2 ![![71, 0, 0], ![32, 1, 0]]
  ![-1129, -13, 23] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![142, 0, 0], ![64, 2, 0]]
    hsu := by decide
    w := ![![-2258, -26, 46], ![1240, 18, -26]]
    hw := by decide
    g := ![![![255, 130, 38], ![195, 0, 0]], ![![155, 79, 23], ![118, 0, 0]]]
    h := ![![![-7119, -310, -5], ![15760, 189, 0]], ![![3892, 141, 1], ![-8616, -42, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {2} * I71N1 =  Ideal.span {B.equivFun.symm ![-1129, -13, 23]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 2 ![![71, 0, 0], ![35, 1, 0]]
  ![-305, -197, -33] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![142, 0, 0], ![70, 2, 0]]
    hsu := by decide
    w := ![![-610, -394, -66], ![-3704, -2382, -394]]
    hw := by decide
    g := ![![![-20262, 3837, 494], ![-8211, 0, 0]], ![![-9393, 1778, 229], ![-3805, 0, 0]]]
    h := ![![![80, -21142, -1175], ![-171, 41696, 0]], ![![668, -128377, -7135], ![-1408, 253194, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {2} * I71N2 =  Ideal.span {B.equivFun.symm ![-305, -197, -33]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS2 
