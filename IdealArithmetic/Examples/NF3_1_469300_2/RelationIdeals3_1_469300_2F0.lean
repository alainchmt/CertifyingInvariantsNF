import IdealArithmetic.Examples.NF3_1_469300_2.PrimesBelow3_1_469300_2F0
import IdealArithmetic.Examples.NF3_1_469300_2.ClassGroupData3_1_469300_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 32 ![![2, 0, 0], ![0, 1, 0]]
  ![4, 1, 0] ![![32, 0, 0], ![-47, -4, 1]] where
    su := ![![64, 0, 0], ![0, 32, 0]]
    hsu := by decide
    w := ![![128, 32, 0], ![192, 32, 0]]
    hw := by decide
    g := ![![![-1, 0, 0], ![1, 0, 0]], ![![3, 0, 0], ![-2, 0, 0]]]
    h := ![![![2, 0, 0], ![1, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {32} * I2N0 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 10*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 36 ![![3, 0, 0], ![-64, -5, 1]]
  ![-8, -7, -1] ![![36, 0, 0], ![-61, -6, 1]] where
    su := ![![108, 0, 0], ![-2304, -180, 36]]
    hsu := by decide
    w := ![![-288, -252, -36], ![108, 0, 0]]
    hw := by decide
    g := ![![![354, 23, -5], ![-575, -126, 0]], ![![-6844, -435, 96], ![11748, 2534, 0]]]
    h := ![![![40, 1, -1], ![2, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {36} * I3N0 =  Ideal.span {B.equivFun.symm ![-8, -7, -1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 64 ![![3, 0, 0], ![-1, 1, 0]]
  ![4, 1, 0] ![![192, 0, 0], ![-15, -4, 1]] where
    su := ![![192, 0, 0], ![-64, 64, 0]]
    hsu := by decide
    w := ![![768, 192, 0], ![320, 64, 0]]
    hw := by decide
    g := ![![![-1, 0, 0], ![3, 0, 0]], ![![7, 1, 0], ![-17, -3, 0]]]
    h := ![![![10, -5, 0], ![18, 0, 0]], ![![4, -2, 0], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {64} * I3N1 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 11*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 18 ![![5, 0, 0], ![0, 1, 0]]
  ![110, 13, -2] ![![18, 0, 0], ![-61, -6, 1]] where
    su := ![![90, 0, 0], ![0, 18, 0]]
    hsu := by decide
    w := ![![1980, 234, -36], ![2790, 162, -36]]
    hw := by decide
    g := ![![![-1042, 18, 9], ![3679, 640, 0]], ![![11, 2, 0], ![2, 0, 0]]]
    h := ![![![22, 2, 0], ![3, -2, 0]], ![![31, 2, -1], ![-1, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {18} * I5N0 =  Ideal.span {B.equivFun.symm ![110, 13, -2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E11RS0 : RelationCertificate Table 4 ![![11, 0, 0], ![1, 1, 0]]
  ![72, 5, -1] ![![4, 0, 0], ![-61, -6, 1]] where
    su := ![![44, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![288, 20, -4], ![-212, -72, 8]]
    hw := by decide
    g := ![![![444, -689, 43], ![-5391, -870, 0]], ![![85, -63, 4], ![-537, -87, 0]]]
    h := ![![![12, 5, -1], ![-60, 10, 0]], ![![-5, -5, -3], ![2, 35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {4} * I11N0 =  Ideal.span {B.equivFun.symm ![72, 5, -1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 24 ![![11, 0, 0], ![2, 1, 0]]
  ![-44, -13, -1] ![![24, 0, 0], ![-571, -56, 9]] where
    su := ![![264, 0, 0], ![48, 24, 0]]
    hsu := by decide
    w := ![![-1056, -312, -24], ![1944, 672, 48]]
    hw := by decide
    g := ![![![37746, -172631, -7779], ![-491445, -82316, 0]], ![![8394, -36478, -1652], ![-103942, -17413, 0]]]
    h := ![![![-1704, -885, -17], ![9350, 186, 0]], ![![3133, 1625, 30], ![-17191, -328, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {24} * I11N1 =  Ideal.span {B.equivFun.symm ![-44, -13, -1]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 144 ![![11, 0, 0], ![-3, 1, 0]]
  ![428, 19, -5] ![![144, 0, 0], ![229, 68, -3]] where
    su := ![![1584, 0, 0], ![-432, 144, 0]]
    hsu := by decide
    w := ![![61632, 2736, -720], ![-52848, 1440, 288]]
    hw := by decide
    g := ![![![-323881, 158015, 51988], ![-441317, -129562, 0]], ![![102857, -50341, -16540], ![140557, 41227, 0]]]
    h := ![![![652, -213, 3], ![2248, -38, 0]], ![![-557, 185, -3], ![-1920, 35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {144} * I11N2 =  Ideal.span {B.equivFun.symm ![428, 19, -5]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 16 ![![13, 0, 0], ![1, 1, 0]]
  ![12, -1, 0] ![![16, 0, 0], ![-63, -4, 1]] where
    su := ![![208, 0, 0], ![16, 16, 0]]
    hsu := by decide
    w := ![![192, -16, 0], ![-1136, -80, 16]]
    hw := by decide
    g := ![![![7, 1, 0], ![1, 0, 0]], ![![6, 1, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![12, 0, 0]], ![![-6, -6, -5], ![7, 66, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {16} * I13N0 =  Ideal.span {B.equivFun.symm ![12, -1, 0]} * (J0 ^ 8*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_0 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 2 ![![13, 0, 0], ![6, 1, 0]]
  ![6, 1, 0] ![![2, 0, 0], ![-63, -6, 1]] where
    su := ![![26, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![12, 2, 0], ![2, -4, 0]]
    hw := by decide
    g := ![![![2, 0, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![18, 3, 0], ![-38, 0, 0]], ![![1, 0, 0], ![-2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {2} * I13N1 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E13RS1 


noncomputable def E19RS0 : RelationCertificate Table 24 ![![19, 0, 0], ![0, 1, 0]]
  ![-76, -5, 1] ![![24, 0, 0], ![-571, -56, 9]] where
    su := ![![456, 0, 0], ![0, 24, 0]]
    hsu := by decide
    w := ![![-1824, -120, 24], ![5016, 936, -120]]
    hw := by decide
    g := ![![![263, 30, -4], ![23, 2, 0]], ![![333, 39, -5], ![32, 3, 0]]]
    h := ![![![-4, 0, 0], ![-5, 1, 0]], ![![11, 2, 0], ![1, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {24} * I19N0 =  Ideal.span {B.equivFun.symm ![-76, -5, 1]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E19RS0 


noncomputable def E23RS1 : RelationCertificate Table 288 ![![23, 0, 0], ![-9, 1, 0]]
  ![-28, -11, 1] ![![288, 0, 0], ![4473, 524, -71]] where
    su := ![![6624, 0, 0], ![-2592, 288, 0]]
    hsu := by decide
    w := ![![-8064, -3168, 288], ![370656, 33120, -6048]]
    hw := by decide
    g := ![![![27897448, -114453306, -13126719], ![228330821, 38152640, 0]], ![![-10726193, 43992625, 5045632], ![-87764459, -14664921, 0]]]
    h := ![![![-82352, 10221, -119], ![-210452, 2738, 0]], ![![3815676, -473047, 5454], ![9751029, -125463, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {288} * I23N1 =  Ideal.span {B.equivFun.symm ![-28, -11, 1]} * (J0 ^ 7*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_2 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 64 ![![29, 0, 0], ![7, 1, 0]]
  ![28, 11, 1] ![![64, 0, 0], ![-1213, -108, 19]] where
    su := ![![1856, 0, 0], ![448, 64, 0]]
    hsu := by decide
    w := ![![1792, 704, 64], ![4416, 448, -64]]
    hw := by decide
    g := ![![![-59032, 118548, -11475], ![924605, 155862, 0]], ![![-14844, 31103, -3015], ![242191, 40821, 0]]]
    h := ![![![7672, 1194, 14], ![-31780, -405, 0]], ![![18773, 2920, 34], ![-77764, -987, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {64} * I29N0 =  Ideal.span {B.equivFun.symm ![28, 11, 1]} * (J0 ^ 11*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_0 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 288 ![![29, 0, 0], ![-4, 1, 0]]
  ![-116, -25, -1] ![![288, 0, 0], ![4473, 524, -71]] where
    su := ![![8352, 0, 0], ![-1152, 288, 0]]
    hsu := by decide
    w := ![![-33408, -7200, -288], ![-43488, -26784, -2592]]
    hw := by decide
    g := ![![![10553157, -43293518, -4965376], ![86369329, 14431776, 0]], ![![-772105, 3156514, 362100], ![-6297596, -1052317, 0]]]
    h := ![![![-141964, 36113, -156], ![-1029210, 4523, 0]], ![![-184151, 46844, -203], ![-1335057, 5878, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {288} * I29N1 =  Ideal.span {B.equivFun.symm ![-116, -25, -1]} * (J0 ^ 7*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_2 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 48 ![![29, 0, 0], ![-3, 1, 0]]
  ![-52, -5, 1] ![![48, 0, 0], ![-433, -36, 7]] where
    su := ![![1392, 0, 0], ![-144, 48, 0]]
    hsu := by decide
    w := ![![-2496, -240, 48], ![-4464, -48, 48]]
    hw := by decide
    g := ![![![269, 26, -2], ![-69, -16, 0]], ![![9, 1, 0], ![-5, -1, 0]]]
    h := ![![![-62, 23, -1], ![-582, 30, 0]], ![![-111, 39, -1], ![-1042, 30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {48} * I29N2 =  Ideal.span {B.equivFun.symm ![-52, -5, 1]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E29RS2 
