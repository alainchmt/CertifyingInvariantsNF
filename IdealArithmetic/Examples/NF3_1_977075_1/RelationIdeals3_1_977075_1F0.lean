import IdealArithmetic.Examples.NF3_1_977075_1.PrimesBelow3_1_977075_1F0
import IdealArithmetic.Examples.NF3_1_977075_1.ClassGroupData3_1_977075_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 256 ![![2, 0, 0], ![-49, 5, 1]]
  ![-171, -27, -1] ![![256, 0, 0], ![-28, 1, 0]] where
    su := ![![512, 0, 0], ![-12544, 1280, 256]]
    hsu := by decide
    w := ![![-43776, -6912, -256], ![5120, 512, 0]]
    hw := by decide
    g := ![![![-1094, -2592817, 92602], ![-10001, -23706113, 0]], ![![23239, 55007830, -1964595], ![212469, 502936320, 0]]]
    h := ![![![37, -26, -3], ![5, 0, 0]], ![![10, 1, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {256} * I2N1 =  Ideal.span {B.equivFun.symm ![-171, -27, -1]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 64 ![![5, 0, 0], ![-2, 1, 0]]
  ![2051, -333, -55] ![![64, 0, 0], ![-28, 1, 0]] where
    su := ![![320, 0, 0], ![-128, 64, 0]]
    hsu := by decide
    w := ![![131264, -21312, -3520], ![-39168, 7360, 1152]]
    hw := by decide
    g := ![![![12543, 2158335, -77096], ![28271, 4934475, 0]], ![![-2798, -429757, 15344], ![-5451, -982800, 0]]]
    h := ![![![336399, -185445, 8681], ![839972, -43460, 0]], ![![-100640, 55469, -2590], ![-251294, 12968, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {64} * I5N0 =  Ideal.span {B.equivFun.symm ![2051, -333, -55]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![-52, 7, 1]]
  ![8601, -2765, 255] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![-104, 14, 2]]
    hsu := by decide
    w := ![![17202, -5530, 510], ![-84660, 27216, -2510]]
    hw := by decide
    g := ![![![-193, 4, 97], ![2, -189, 0]], ![![248, -71, -727], ![-34, 1431, 0]]]
    h := ![![![3, -230, 60], ![-165, 0, 0]], ![![74, 1120, -297], ![824, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![8601, -2765, 255]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 256 ![![7, 0, 0], ![-1, 1, 0]]
  ![11635, -3741, 345] ![![256, 0, 0], ![-28, 1, 0]] where
    su := ![![1792, 0, 0], ![-256, 256, 0]]
    hsu := by decide
    w := ![![2978560, -957696, 88320], ![-440320, 141568, -13056]]
    hw := by decide
    g := ![![![-34511, -81766215, 2920266], ![-315501, -747588090, 0]], ![![1021, 2357675, -84204], ![9341, 21556221, 0]]]
    h := ![![![3652, -2545, 70], ![13929, -145, 0]], ![![-538, 375, -11], ![-2046, 26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {256} * I7N1 =  Ideal.span {B.equivFun.symm ![11635, -3741, 345]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 64 ![![11, 0, 0], ![-4, 1, 0]]
  ![-127, 17, 3] ![![64, 0, 0], ![-28, 1, 0]] where
    su := ![![704, 0, 0], ![-256, 64, 0]]
    hsu := by decide
    w := ![![-8128, 1088, 192], ![2560, -384, -64]]
    hw := by decide
    g := ![![![-268809, -46852348, 1673641], ![-614420, -107113025, 0]], ![![122200, 21296552, -760747], ![279313, 48687809, 0]]]
    h := ![![![-209, 56, -1], ![-543, 14, 0]], ![![72, -18, 0], ![188, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {64} * I11N0 =  Ideal.span {B.equivFun.symm ![-127, 17, 3]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E11RS0 


noncomputable def E13RS0 : RelationCertificate Table 2 ![![13, 0, 0], ![-45, -2, 1]]
  ![-199, 29, 5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![26, 0, 0], ![-90, -4, 2]]
    hsu := by decide
    w := ![![-398, 58, 10], ![-1660, 166, 34]]
    hw := by decide
    g := ![![![-101, 26, -156], ![13, 306, 0]], ![![-557, 143, 519], ![72, -1071, 0]]]
    h := ![![![2, 3, 0], ![5, 0, 0]], ![![-5, 9, 0], ![17, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {2} * I13N0 =  Ideal.span {B.equivFun.symm ![-199, 29, 5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 256 ![![13, 0, 0], ![1, 1, 0]]
  ![173, -67, 7] ![![256, 0, 0], ![-28, 1, 0]] where
    su := ![![3328, 0, 0], ![256, 256, 0]]
    hsu := by decide
    w := ![![44288, -17152, 1792], ![-7168, 2560, -256]]
    hw := by decide
    g := ![![![-4549823611, -10776582217004, 384883739668], ![-41598387304, -98530237355011, 0]], ![![301, 652193, -23293], ![2749, 5963006, 0]]]
    h := ![![![26, 7, 0], ![-165, 7, 0]], ![![-3, -3, -3], ![11, 38, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {256} * I13N1 =  Ideal.span {B.equivFun.symm ![173, -67, 7]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 16 ![![17, 0, 0], ![4, 1, 0]]
  ![-11, -11, -1] ![![16, 0, 0], ![4, 1, 0]] where
    su := ![![272, 0, 0], ![64, 16, 0]]
    hsu := by decide
    w := ![![-176, -176, -16], ![288, -128, -16]]
    hw := by decide
    g := ![![![-12131063, 824912650, 206986355], ![48524276, -3311781677, 0]], ![![-2140874, 145579131, 36528587], ![8563487, -584457393, 0]]]
    h := ![![![-483, -133, -3], ![2050, 50, 0]], ![![730, 194, 3], ![-3098, -52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {16} * I17N0 =  Ideal.span {B.equivFun.symm ![-11, -11, -1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 2 ![![17, 0, 0], ![8, 1, 0]]
  ![-35, 11, -1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![34, 0, 0], ![16, 2, 0]]
    hsu := by decide
    w := ![![-70, 22, -2], ![332, -108, 10]]
    hw := by decide
    g := ![![![9, -4, -26], ![0, 51, 0]], ![![14, -3, -11], ![-1, 21, 0]]]
    h := ![![![-179, -37, -2], ![376, 33, 0]], ![![774, 146, 7], ![-1624, -114, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![-35, 11, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 256 ![![19, 0, 0], ![-9, 1, 0]]
  ![-689, -257, -19] ![![256, 0, 0], ![-28, 1, 0]] where
    su := ![![4864, 0, 0], ![-2304, 256, 0]]
    hsu := by decide
    w := ![![-176384, -65792, -4864], ![25600, 5120, 256]]
    hw := by decide
    g := ![![![4172649, 9883232532, -352977913], ![38150082, 90362345605, 0]], ![![-2195991, -5201443315, 185768634], ![-20077779, -47556770182, 0]]]
    h := ![![![-1691717, 220198, -3584], ![-3571326, 68077, 0]], ![![247168, -32132, 519], ![521788, -9860, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {256} * I19N0 =  Ideal.span {B.equivFun.symm ![-689, -257, -19]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 4 ![![19, 0, 0], ![-2, 1, 0]]
  ![439, -141, 13] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![76, 0, 0], ![-8, 4, 0]]
    hsu := by decide
    w := ![![1756, -564, 52], ![-4316, 1388, -128]]
    hw := by decide
    g := ![![![25, 4, 8288952], ![4, -33155807, 0]], ![![-7, 1, -1308873], ![3, 5235493, 0]]]
    h := ![![![3435, -1730, 9], ![32413, -158, 0]], ![![-8439, 4252, -23], ![-79631, 405, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {4} * I19N1 =  Ideal.span {B.equivFun.symm ![439, -141, 13]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 8 ![![23, 0, 0], ![-7, 1, 0]]
  ![1247, -401, 37] ![![8, 0, 0], ![4, 1, 0]] where
    su := ![![184, 0, 0], ![-56, 8, 0]]
    hsu := by decide
    w := ![![9976, -3208, 296], ![-7296, 2344, -216]]
    hw := by decide
    g := ![![![65, 180, 47], ![59, -390, 0]], ![![-1, -51, -13], ![-5, 105, 0]]]
    h := ![![![5065, -771, 7], ![16464, -124, 0]], ![![-3690, 568, -6], ![-11994, 111, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {8} * I23N1 =  Ideal.span {B.equivFun.symm ![1247, -401, 37]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E23RS1 


noncomputable def E31RS0 : RelationCertificate Table 2 ![![31, 0, 0], ![1, 1, 0]]
  ![-143, 15, 3] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![62, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-286, 30, 6], ![-996, 76, 18]]
    hw := by decide
    g := ![![![355, -92, -36], ![-44, 93, 0]], ![![-101, 26, -3], ![13, 0, 0]]]
    h := ![![![-5, -5, -5], ![12, 158, 0]], ![![-17, -17, -17], ![29, 536, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {2} * I31N0 =  Ideal.span {B.equivFun.symm ![-143, 15, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 16 ![![31, 0, 0], ![13, 1, 0]]
  ![685, -19, -9] ![![16, 0, 0], ![4, 1, 0]] where
    su := ![![496, 0, 0], ![208, 16, 0]]
    hsu := by decide
    w := ![![10960, -304, -144], ![5728, -48, -64]]
    hw := by decide
    g := ![![![-12831, 879057, 220584], ![51737, -3529295, 0]], ![![-5599, 381265, 95668], ![22438, -1530683, 0]]]
    h := ![![![2503, 220, 2], ![-5916, -71, 0]], ![![1304, 114, 1], ![-3082, -35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {16} * I31N1 =  Ideal.span {B.equivFun.symm ![685, -19, -9]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 16 ![![31, 0, 0], ![-15, 1, 0]]
  ![17641, -5671, 523] ![![16, 0, 0], ![4, 1, 0]] where
    su := ![![496, 0, 0], ![-240, 16, 0]]
    hsu := by decide
    w := ![![282256, -90736, 8368], ![-103072, 33136, -3056]]
    hw := by decide
    g := ![![![-7111, 481912, 120919], ![28349, -1934676, 0]], ![![3331, -227128, -56990], ![-13353, 911835, 0]]]
    h := ![![![4464541, -351033, 3567], ![9225542, -110054, 0]], ![![-1630312, 128193, -1303], ![-3368882, 40202, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {16} * I31N2 =  Ideal.span {B.equivFun.symm ![17641, -5671, 523]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E31RS2 
