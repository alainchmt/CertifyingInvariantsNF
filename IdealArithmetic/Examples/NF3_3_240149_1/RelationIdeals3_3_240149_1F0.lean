import IdealArithmetic.Examples.NF3_3_240149_1.PrimesBelow3_3_240149_1F0
import IdealArithmetic.Examples.NF3_3_240149_1.ClassGroupData3_3_240149_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 4 ![![2, 0, 0], ![-16, 1, 1]]
  ![-10, 3, -1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![8, 0, 0], ![-64, 4, 4]]
    hsu := by decide
    w := ![![-40, 12, -4], ![32, -28, 12]]
    hw := by decide
    g := ![![![-1, -1, 1], ![4, -1, 0]], ![![8, -9, -11], ![6, 7, 0]]]
    h := ![![![3, 1, -1], ![1, 0, 0]], ![![12, -4, 1], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {4} * I2N0 =  Ideal.span {B.equivFun.symm ![-10, 3, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![0, 0, -5], ![0, 2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, 0, -5], ![0, 2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![0, 0, -5], ![0, 3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, 0, -5], ![0, 3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 9 ![![3, 0, 0], ![-15, 1, 1]]
  ![-33, -1, 2] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![27, 0, 0], ![-135, 9, 9]]
    hsu := by decide
    w := ![![-297, -9, 18], ![0, 18, -9]]
    hw := by decide
    g := ![![![-41, 157, -269], ![37, 484, 0]], ![![134, -475, 806], ![-92, -1452, 0]]]
    h := ![![![14, -2, -1], ![5, 0, 0]], ![![10, 0, -1], ![2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {9} * I3N1 =  Ideal.span {B.equivFun.symm ![-33, -1, 2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 12 ![![5, 0, 0], ![1, 1, 0]]
  ![-18, 1, 1] ![![12, 0, 0], ![6, 1, 0]] where
    su := ![![60, 0, 0], ![12, 12, 0]]
    hsu := by decide
    w := ![![-216, 12, 12], ![-156, 12, 12]]
    hw := by decide
    g := ![![![-4, -18, -15], ![1, 36, 0]], ![![-4, -9, -7], ![5, 17, 0]]]
    h := ![![![-10599, 5494, 441], ![-1021, 0, -1102]], ![![-7810, 4048, 325], ![-751, 0, -812]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {12} * I5N0 =  Ideal.span {B.equivFun.symm ![-18, 1, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 12 ![![5, 0, 0], ![-15, 0, 1]]
  ![-6, 1, 1] ![![12, 0, 0], ![6, 1, 0]] where
    su := ![![60, 0, 0], ![-180, 0, 12]]
    hsu := by decide
    w := ![![-72, 12, 12], ![-84, 24, 12]]
    hw := by decide
    g := ![![![-78, -756, -637], ![-102, 1529, 0]], ![![237, 2336, 1969], ![323, -4726, 0]]]
    h := ![![![6, 11, -3], ![22, -6, 0]], ![![-1, 13, -3], ![23, -7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {12} * I5N1 =  Ideal.span {B.equivFun.symm ![-6, 1, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 12 ![![5, 0, 0], ![32, 1, -2]]
  ![-30, 1, 1] ![![12, 0, 0], ![6, 1, 0]] where
    su := ![![60, 0, 0], ![384, 12, -24]]
    hsu := by decide
    w := ![![-360, 12, 12], ![-228, 0, 12]]
    hw := by decide
    g := ![![![-8, -21, -17], ![8, 41, 0]], ![![-20, -134, -112], ![-7, 269, 0]]]
    h := ![![![-3704, 20040, -9467], ![-15751, 5278, 0]], ![![-2333, 12552, -5929], ![-9864, 3306, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {12} * I5N2 =  Ideal.span {B.equivFun.symm ![-30, 1, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 4 ![![7, 0, 0], ![2, 1, 0]]
  ![14, -1, -1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![28, 0, 0], ![8, 4, 0]]
    hsu := by decide
    w := ![![56, -4, -4], ![76, -12, -8]]
    hw := by decide
    g := ![![![2, 8, 21], ![4, -17, 0]], ![![2, 2, 9], ![3, -7, 0]]]
    h := ![![![-173, -393, -1018], ![-100, 1425, 0]], ![![-238, -544, -1411], ![-145, 1975, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4} * I7N0 =  Ideal.span {B.equivFun.symm ![14, -1, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![-3, 1, 0]]
  ![0, -2, 1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![33, 0, 0], ![-9, 3, 0]]
    hsu := by decide
    w := ![![0, -6, 3], ![-51, 24, -9]]
    hw := by decide
    g := ![![![0, 95631, 1089153], ![31878, -650835, -13282]], ![![0, -16293, -185559], ![-5431, 110883, 2263]]]
    h := ![![![-5, 17, -29], ![3, 64, 0]], ![![318, -1091, 1847], ![-183, -4064, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![0, -2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 6 ![![13, 0, 0], ![4, 1, 0]]
  ![-12, 1, 1] ![![6, 0, 0], ![0, 1, 0]] where
    su := ![![78, 0, 0], ![24, 6, 0]]
    hsu := by decide
    w := ![![-72, 6, 6], ![-48, 12, 6]]
    hw := by decide
    g := ![![![-556662, -1, -2783304], ![5, 3339965, 0]], ![![-171341, 0, -856700], ![1, 1028040, 0]]]
    h := ![![![584, 2799, 3537], ![398, -9196, 0]], ![![396, 1897, 2397], ![269, -6232, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {6} * I13N0 =  Ideal.span {B.equivFun.symm ![-12, 1, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS0 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![2, 1, 0]]
  ![-2, 1, 1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![68, 0, 0], ![8, 4, 0]]
    hsu := by decide
    w := ![![-8, 4, 4], ![-52, 24, 8]]
    hw := by decide
    g := ![![![-148, -493, -1356], ![-197, 1084, 0]], ![![-39, -124, -339], ![-46, 271, 0]]]
    h := ![![![5, 11, 28], ![4, -95, 0]], ![![34, 72, 181], ![12, -615, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![-2, 1, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 9 ![![19, 0, 0], ![-4, 1, 0]]
  ![-21, 7, 4] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![171, 0, 0], ![-36, 9, 0]]
    hsu := by decide
    w := ![![-189, 63, 36], ![-126, 54, 27]]
    hw := by decide
    g := ![![![-1, -5, 7], ![7, -12, 0]], ![![2, -1, 1], ![5, -2, 0]]]
    h := ![![![2467, -10716, 13466], ![-1069, -51170, 0]], ![![1654, -7191, 9037], ![-725, -34340, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {9} * I19N1 =  Ideal.span {B.equivFun.symm ![-21, 7, 4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS1 


noncomputable def E29RS0 : RelationCertificate Table 36 ![![29, 0, 0], ![8, 1, 0]]
  ![222, 1, -11] ![![36, 0, 0], ![6, 1, 0]] where
    su := ![![1044, 0, 0], ![288, 36, 0]]
    hsu := by decide
    w := ![![7992, 36, -396], ![1872, -36, -72]]
    hw := by decide
    g := ![![![269800, 1708676, 1426037], ![92455, -10267469, 0]], ![![74428, 471385, 393412], ![25533, -2832568, 0]]]
    h := ![![![-716, -6719, -4209], ![-428, 24410, 0]], ![![-174, -1578, -988], ![-79, 5730, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {36} * I29N0 =  Ideal.span {B.equivFun.symm ![222, 1, -11]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 36 ![![29, 0, 0], ![12, 1, 0]]
  ![66, -25, -13] ![![36, 0, 0], ![6, 1, 0]] where
    su := ![![1044, 0, 0], ![432, 36, 0]]
    hsu := by decide
    w := ![![2376, -900, -468], ![1008, -396, -216]]
    hw := by decide
    g := ![![![23374, 148005, 123523], ![8017, -889367, 0]], ![![9671, 61241, 51111], ![3323, -368000, 0]]]
    h := ![![![-168, -2843, -1187], ![-162, 6882, 0]], ![![-82, -1208, -504], ![-43, 2922, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {36} * I29N1 =  Ideal.span {B.equivFun.symm ![66, -25, -13]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 18 ![![31, 0, 0], ![-15, 1, 0]]
  ![24, -5, 1] ![![18, 0, 0], ![6, 1, 0]] where
    su := ![![558, 0, 0], ![-270, 18, 0]]
    hsu := by decide
    w := ![![432, -90, 18], ![90, 18, -18]]
    hw := by decide
    g := ![![![11, 97, 82], ![25, -296, 0]], ![![-11, -46, -38], ![7, 137, 0]]]
    h := ![![![-4, 281, -94], ![29, 583, 0]], ![![11, 47, -16], ![29, 99, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {18} * I31N1 =  Ideal.span {B.equivFun.symm ![24, -5, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS1 
