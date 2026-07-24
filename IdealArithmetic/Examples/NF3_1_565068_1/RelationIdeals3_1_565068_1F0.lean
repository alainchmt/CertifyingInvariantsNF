import IdealArithmetic.Examples.NF3_1_565068_1.PrimesBelow3_1_565068_1F0
import IdealArithmetic.Examples.NF3_1_565068_1.ClassGroupData3_1_565068_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 33 ![![2, 0, 0], ![1, 1, 0]]
  ![6, 4, 1] ![![33, 0, 0], ![13, 1, 0]] where
    su := ![![66, 0, 0], ![33, 33, 0]]
    hsu := by decide
    w := ![![198, 132, 33], ![33, 33, 33]]
    hw := by decide
    g := ![![![9, -1369, -489], ![-16, 3228, 0]], ![![-7, 456, 163], ![16, -1076, 0]]]
    h := ![![![-18, -20, -2], ![42, 1, 0]], ![![-22, -23, -2], ![45, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {33} * I2N0 =  Ideal.span {B.equivFun.symm ![6, 4, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 3 ![![3, 0, 0], ![0, 1, 0]]
  ![-28242, 287, -949] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![9, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![-84726, 861, -2847], ![14463, -147, 486]]
    hw := by decide
    g := ![![![-8, -5, -1], ![-4, 2, 0]], ![![-30, -23, -10], ![-15, 1, 0]]]
    h := ![![![-9414, -398, -233], ![1531, -50, 0]], ![![1607, 66, 39], ![-256, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {3} * I3N0 =  Ideal.span {B.equivFun.symm ![-28242, 287, -949]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![0, 1, 0]]
  ![-105, -82, -25] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![15, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![-315, -246, -75], ![1020, 456, -435]]
    hw := by decide
    g := ![![![28327, -3118, 1046], ![8405, 0, 0]], ![![-8567, 944, -313], ![-2541, -2, 0]]]
    h := ![![![-21, -16, -5], ![-2, 0, 0]], ![![68, 29, -29], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![-105, -82, -25]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 3 ![![5, 0, 0], ![-1, 1, 0]]
  ![3, 2, 0] ![![3, 0, 0], ![20, 0, 1]] where
    su := ![![15, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![9, 6, 0], ![-30, -18, 3]]
    hw := by decide
    g := ![![![-5, 2, 3], ![-29, 0, 0]], ![![-7, -1, -2], ![16, 0, 0]]]
    h := ![![![1244, 829, 28], ![-83, 0, 140]], ![![-4229, -2819, -95], ![285, 0, -476]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {3} * I5N1 =  Ideal.span {B.equivFun.symm ![3, 2, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 121 ![![7, 0, 0], ![2, 1, 0]]
  ![3418, -35, 115] ![![121, 0, 0], ![-9, 1, 0]] where
    su := ![![847, 0, 0], ![242, 121, 0]]
    hsu := by decide
    w := ![![413578, -4235, 13915], ![-35937, 363, -1210]]
    hw := by decide
    g := ![![![-3383, -5535400, 3459860], ![-45483, -83728611, 0]], ![![-1378, -2256167, 1410200], ![-18523, -34126839, 0]]]
    h := ![![![456946, 272908, 74490], ![-1597602, -104263, 0]], ![![-39707, -23716, -6475], ![138826, 9063, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {121} * I7N0 =  Ideal.span {B.equivFun.symm ![3418, -35, 115]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 121 ![![11, 0, 0], ![17, 4, 1]]
  ![-77074, 783, -2590] ![![121, 0, 0], ![-9, 1, 0]] where
    su := ![![1331, 0, 0], ![2057, 484, 121]]
    hsu := by decide
    w := ![![-9325954, 94743, -313390], ![810216, -8228, 27225]]
    hw := by decide
    g := ![![![2756278, 4508654043, -2818100185], ![37056623, 68198024476, 0]], ![![4206955, 6881631536, -4301311859], ![56560167, 104091746996, 0]]]
    h := ![![![-2273, 1185, 43], ![-3063, 0, 0]], ![![193, -104, -4], ![269, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {121} * I11N0 =  Ideal.span {B.equivFun.symm ![-77074, 783, -2590]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![11, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![9, 4, 0], ![-44, 0, 0]], ![![-2, -1, 0], ![12, 0, 0]]]
    h := ![![![9, 4, 0], ![-44, 0, 0]], ![![-2, -1, 0], ![12, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 363 ![![13, 0, 0], ![1, 1, 0]]
  ![525, 416, 137] ![![363, 0, 0], ![112, 1, 0]] where
    su := ![![4719, 0, 0], ![363, 363, 0]]
    hsu := by decide
    w := ![![190575, 151008, 49731], ![52635, 43560, 17424]]
    hw := by decide
    g := ![![![1771680, -2282584045, -100999984], ![-5741204, 7332599544, 0]], ![![150520, -194080961, -8587713], ![-487883, 623467936, 0]]]
    h := ![![![-846, -855, 9], ![11523, 4, 0]], ![![-190, -193, 1], ![2615, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {363} * I13N0 =  Ideal.span {B.equivFun.symm ![525, 416, 137]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 363 ![![13, 0, 0], ![5, 1, 0]]
  ![-5493, 56, -184] ![![363, 0, 0], ![112, 1, 0]] where
    su := ![![4719, 0, 0], ![1815, 363, 0]]
    hsu := by decide
    w := ![![-1993959, 20328, -66792], ![-606936, 6171, -20328]]
    hw := by decide
    g := ![![![-121, 117315, 5191], ![392, -376865, 0]], ![![-105, 53674, 2375], ![340, -172425, 0]]]
    h := ![![![-5047171, -1321116, -259823], ![13121546, 675503, 0]], ![![-1536304, -402133, -79087], ![3994056, 205615, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {363} * I13N1 =  Ideal.span {B.equivFun.symm ![-5493, 56, -184]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 363 ![![13, 0, 0], ![6, 1, 0]]
  ![732, -7, 23] ![![363, 0, 0], ![112, 1, 0]] where
    su := ![![4719, 0, 0], ![2178, 363, 0]]
    hsu := by decide
    w := ![![265716, -2541, 8349], ![80949, -726, 2541]]
    hw := by decide
    g := ![![![1207854, -1556453611, -68870106], ![-3914741, 4999969695, 0]], ![![703037, -905931718, -40085752], ![-2278593, 2910225595, 0]]]
    h := ![![![-210, 8634, 6201], ![577, -16118, 0]], ![![-65, 2630, 1889], ![178, -4910, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {363} * I13N2 =  Ideal.span {B.equivFun.symm ![732, -7, 23]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS2 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![-6, 1, 0]]
  ![3, 4, 4] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![51, 0, 0], ![-18, 3, 0]]
    hsu := by decide
    w := ![![9, 12, 12], ![-177, -105, 24]]
    hw := by decide
    g := ![![![-1551, 152, -109], ![-466, 31, 0]], ![![685, -70, 42], ![207, -10, 0]]]
    h := ![![![9, 2, -3], ![25, 11, 0]], ![![-121, 19, -1], ![-333, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![3, 4, 4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS1 


noncomputable def E23RS1 : RelationCertificate Table 33 ![![23, 0, 0], ![6, 1, 0]]
  ![1365, -14, 46] ![![33, 0, 0], ![13, 1, 0]] where
    su := ![![759, 0, 0], ![198, 33, 0]]
    hsu := by decide
    w := ![![45045, -462, 1518], ![15675, -165, 528]]
    hw := by decide
    g := ![![![-2, -611, -218], ![5, 1440, 0]], ![![-11, -186, -66], ![27, 436, 0]]]
    h := ![![![1119, 190, 12], ![-4062, -46, 0]], ![![389, 63, 2], ![-1412, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {33} * I23N1 =  Ideal.span {B.equivFun.symm ![1365, -14, 46]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E31RS0 : RelationCertificate Table 3 ![![31, 0, 0], ![10, 1, 0]]
  ![6, 5, 2] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![93, 0, 0], ![30, 3, 0]]
    hsu := by decide
    w := ![![18, 15, 6], ![-84, -42, 27]]
    hw := by decide
    g := ![![![-659, 68, -36], ![-196, 7, 0]], ![![-181, 16, -15], ![-52, 5, 0]]]
    h := ![![![86, 2, -3], ![-266, 19, 0]], ![![-408, -55, -6], ![1262, 39, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {3} * I31N0 =  Ideal.span {B.equivFun.symm ![6, 5, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E31RS0 
