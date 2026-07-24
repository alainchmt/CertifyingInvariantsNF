import IdealArithmetic.Examples.NF3_1_293891_1.PrimesBelow3_1_293891_1F1
import IdealArithmetic.Examples.NF3_1_293891_1.ClassGroupData3_1_293891_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 2 ![![37, 0, 0], ![4, 1, 0]]
  ![33, 3, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![74, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![66, 6, 2], ![124, 10, 4]]
    hw := by decide
    g := ![![![-819, 4101, 4925], ![1643, -9849, 0]], ![![-97, 489, 588], ![197, -1176, 0]]]
    h := ![![![193, 48, 0], ![-1777, 1, 0]], ![![366, 91, 0], ![-3370, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {2} * I37N0 =  Ideal.span {B.equivFun.symm ![33, 3, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 16 ![![37, 0, 0], ![-8, 1, 0]]
  ![-31, 3, 3] ![![16, 0, 0], ![-1, 1, 0]] where
    su := ![![592, 0, 0], ![-128, 16, 0]]
    hsu := by decide
    w := ![![-496, 48, 48], ![304, -112, 0]]
    hw := by decide
    g := ![![![-43, 30, -36], ![18, 555, 0]], ![![7, -8, 8], ![11, -125, 0]]]
    h := ![![![-115, 15, 0], ![-528, 3, 0]], ![![87, -11, 0], ![400, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {16} * I37N1 =  Ideal.span {B.equivFun.symm ![-31, 3, 3]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 16 ![![41, 0, 0], ![-5, 1, 0]]
  ![11, 1, 1] ![![16, 0, 0], ![-1, 1, 0]] where
    su := ![![656, 0, 0], ![-80, 16, 0]]
    hsu := by decide
    w := ![![176, 16, 16], ![80, -16, 0]]
    hw := by decide
    g := ![![![-6, -1938, 1945], ![-106, -31119, 0]], ![![2, 251, -253], ![31, 4048, 0]]]
    h := ![![![911, -182, 0], ![7468, 1, 0]], ![![415, -83, 0], ![3402, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {16} * I41N1 =  Ideal.span {B.equivFun.symm ![11, 1, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E41RS1 


noncomputable def E47RS0 : RelationCertificate Table 8 ![![47, 0, 0], ![-17, 1, 0]]
  ![-167, -13, -5] ![![8, 0, 0], ![-1, 1, 0]] where
    su := ![![376, 0, 0], ![-136, 8, 0]]
    hsu := by decide
    w := ![![-1336, -104, -40], ![-288, -24, -8]]
    hw := by decide
    g := ![![![3, 12, -14], ![5, 114, 0]], ![![0, -5, 5], ![3, -41, 0]]]
    h := ![![![-25318, 1640, -9], ![-69987, 418, 0]], ![![-5448, 354, -2], ![-15060, 93, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {8} * I47N0 =  Ideal.span {B.equivFun.symm ![-167, -13, -5]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E47RS0 


noncomputable def E59RS1 : RelationCertificate Table 32 ![![59, 0, 0], ![1, 1, 0]]
  ![59, 1, 1] ![![32, 0, 0], ![-1, 1, 0]] where
    su := ![![1888, 0, 0], ![32, 32, 0]]
    hsu := by decide
    w := ![![1888, 32, 32], ![32, 32, 0]]
    hw := by decide
    g := ![![![1, -2, 2], ![0, -65, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![59, 1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {32} * I59N1 =  Ideal.span {B.equivFun.symm ![59, 1, 1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 32 ![![61, 0, 0], ![11, 1, 0]]
  ![641, 51, 19] ![![32, 0, 0], ![-1, 1, 0]] where
    su := ![![1952, 0, 0], ![352, 32, 0]]
    hsu := by decide
    w := ![![20512, 1632, 608], ![1088, 96, 32]]
    hw := by decide
    g := ![![![-116, -120901, 121018], ![-3745, -3872582, 0]], ![![-40, -40950, 40990], ![-1277, -1311681, 0]]]
    h := ![![![160232, 15201, 58], ![-888501, -3519, 0]], ![![8494, 805, 3], ![-47100, -182, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {32} * I61N1 =  Ideal.span {B.equivFun.symm ![641, 51, 19]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 16 ![![67, 0, 0], ![24, 1, 0]]
  ![307, 25, 9] ![![16, 0, 0], ![-1, 1, 0]] where
    su := ![![1072, 0, 0], ![384, 16, 0]]
    hsu := by decide
    w := ![![4912, 400, 144], ![512, 48, 16]]
    hw := by decide
    g := ![![![-4190, -1078085, 1082278], ![-67109, -17316450, 0]], ![![-1564, -402414, 403979], ![-25046, -6463665, 0]]]
    h := ![![![1297, 51, 0], ![-3608, 9, 0]], ![![128, 5, 0], ![-356, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {16} * I67N1 =  Ideal.span {B.equivFun.symm ![307, 25, 9]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E67RS1 


noncomputable def E79RS1 : RelationCertificate Table 8 ![![79, 0, 0], ![20, 1, 0]]
  ![225, -69, -5] ![![8, 0, 0], ![-1, 1, 0]] where
    su := ![![632, 0, 0], ![160, 8, 0]]
    hsu := by decide
    w := ![![1800, -552, -40], ![-680, 424, -64]]
    hw := by decide
    g := ![![![7299, 255968, -259474], ![31090, 2076609, 0]], ![![1945, 63537, -64391], ![7707, 515363, 0]]]
    h := ![![![215, -9, -1], ![-838, 74, 0]], ![![-115, -23, -1], ![450, 71, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {8} * I79N1 =  Ideal.span {B.equivFun.symm ![225, -69, -5]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E79RS1 
