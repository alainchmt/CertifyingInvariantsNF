import IdealArithmetic.Examples.NF3_1_190291_3.PrimesBelow3_1_190291_3F2
import IdealArithmetic.Examples.NF3_1_190291_3.ClassGroupData3_1_190291_3

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 96 ![![83, 0, 0], ![13, 1, 0]]
  ![-881, -83, 17] ![![96, 0, 0], ![-29, 1, 0]] where
    su := ![![7968, 0, 0], ![1248, 96, 0]]
    hsu := by decide
    w := ![![-84576, -7968, 1632], ![29952, 2784, -576]]
    hw := by decide
    g := ![![![810791, 281173063, -9696587], ![2683997, 930872347, 0]], ![![136579, 47362759, -1633361], ![452124, 156802655, 0]]]
    h := ![![![-3915, -317, -1], ![24928, 100, 0]], ![![1378, 107, 0], ![-8774, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {96} * I83N0 =  Ideal.span {B.equivFun.symm ![-881, -83, 17]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 72 ![![83, 0, 0], ![-12, 1, 0]]
  ![-121, 5, 1] ![![72, 0, 0], ![-5, 1, 0]] where
    su := ![![5976, 0, 0], ![-864, 72, 0]]
    hsu := by decide
    w := ![![-8712, 360, 72], ![864, -72, 0]]
    hw := by decide
    g := ![![![-84274, -87798220, 17563015], ![-1213543, -1264537079, 0]], ![![10325, 10754460, -2151305], ![148679, 154893960, 0]]]
    h := ![![![-143, 24, -1], ![-979, 84, 0]], ![![36, -3, 0], ![248, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {72} * I83N1 =  Ideal.span {B.equivFun.symm ![-121, 5, 1]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 16 ![![83, 0, 0], ![-1, 1, 0]]
  ![-81, -3, 1] ![![16, 0, 0], ![3, 1, 0]] where
    su := ![![1328, 0, 0], ![-16, 16, 0]]
    hsu := by decide
    w := ![![-1296, -48, 16], ![16, -16, 0]]
    hw := by decide
    g := ![![![-1, -15, -5], ![2, 79, 0]], ![![0, 0, 0], ![-1, 0, 0]]]
    h := ![![![0, -1, 0], ![81, 1, 0]], ![![0, 1, -1], ![-1, 83, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {16} * I83N2 =  Ideal.span {B.equivFun.symm ![-81, -3, 1]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E83RS2 


noncomputable def E97RS1 : RelationCertificate Table 8 ![![97, 0, 0], ![11, 1, 0]]
  ![-57, -3, 1] ![![8, 0, 0], ![3, 1, 0]] where
    su := ![![776, 0, 0], ![88, 8, 0]]
    hsu := by decide
    w := ![![-456, -24, 8], ![88, 8, 0]]
    hw := by decide
    g := ![![![274, -6566, -2219], ![-714, 17751, 0]], ![![30, -722, -244], ![-79, 1952, 0]]]
    h := ![![![-4157, -389, -1], ![36652, 98, 0]], ![![781, 71, 0], ![-6886, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {8} * I97N1 =  Ideal.span {B.equivFun.symm ![-57, -3, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 48 ![![101, 0, 0], ![-36, 1, 0]]
  ![95, -19, 1] ![![48, 0, 0], ![19, 1, 0]] where
    su := ![![4848, 0, 0], ![-1728, 48, 0]]
    hsu := by decide
    w := ![![4560, -912, 48], ![2064, -192, 0]]
    hw := by decide
    g := ![![![-22, 2810, 148], ![63, -7100, 0]], ![![-4, -988, -52], ![8, 2495, 0]]]
    h := ![![![178243, -5455, 14], ![500068, -1413, 0]], ![![80639, -2456, 6], ![226236, -606, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {48} * I101N1 =  Ideal.span {B.equivFun.symm ![95, -19, 1]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 48 ![![103, 0, 0], ![17, 1, 0]]
  ![97, 19, -1] ![![48, 0, 0], ![19, 1, 0]] where
    su := ![![4944, 0, 0], ![816, 48, 0]]
    hsu := by decide
    w := ![![4656, 912, -48], ![1584, 384, 0]]
    hw := by decide
    g := ![![![-50, 4003, 211], ![103, -10120, 0]], ![![-11, 702, 37], ![25, -1775, 0]]]
    h := ![![![55177, 3365, 7], ![-334302, -722, 0]], ![![18767, 1138, 2], ![-113704, -206, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {48} * I103N1 =  Ideal.span {B.equivFun.symm ![97, 19, -1]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E103RS1 


noncomputable def E109RS1 : RelationCertificate Table 16 ![![109, 0, 0], ![-25, 1, 0]]
  ![31, 13, 1] ![![16, 0, 0], ![3, 1, 0]] where
    su := ![![1744, 0, 0], ![-400, 16, 0]]
    hsu := by decide
    w := ![![496, 208, 16], ![352, 144, 16]]
    hw := by decide
    g := ![![![-44145, 3897845, 1304185], ![235339, -20866956, 0]], ![![9856, -870241, -291175], ![-52539, 4658799, 0]]]
    h := ![![![459, -18, 0], ![2000, 1, 0]], ![![308, -12, 0], ![1342, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {16} * I109N1 =  Ideal.span {B.equivFun.symm ![31, 13, 1]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E109RS1 


noncomputable def E113RS0 : RelationCertificate Table 16 ![![113, 0, 0], ![38, 1, 0]]
  ![327, 37, -7] ![![16, 0, 0], ![3, 1, 0]] where
    su := ![![1808, 0, 0], ![608, 16, 0]]
    hsu := by decide
    w := ![![5232, 592, -112], ![-832, -80, 16]]
    hw := by decide
    g := ![![![-47847, 4225473, 1413807], ![255137, -22620914, 0]], ![![-16582, 1464326, 489951], ![88420, -7839217, 0]]]
    h := ![![![281, -28, -1], ![-827, 106, 0]], ![![-100, -3, 0], ![296, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {16} * I113N0 =  Ideal.span {B.equivFun.symm ![327, 37, -7]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 12 ![![113, 0, 0], ![-30, 1, 0]]
  ![59, 17, 1] ![![12, 0, 0], ![-5, 1, 0]] where
    su := ![![1356, 0, 0], ![-360, 12, 0]]
    hsu := by decide
    w := ![![708, 204, 12], ![-36, 48, 12]]
    hw := by decide
    g := ![![![-16995, -572882, 115254], ![-40653, -1383035, 0]], ![![3207, 107837, -21695], ![7655, 260336, 0]]]
    h := ![![![1033, -34, 0], ![3889, 1, 0]], ![![-21, 1, 0], ![-79, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {12} * I113N1 =  Ideal.span {B.equivFun.symm ![59, 17, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 9 ![![113, 0, 0], ![-8, 1, 0]]
  ![50, 14, 1] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![1017, 0, 0], ![-72, 9, 0]]
    hsu := by decide
    w := ![![450, 126, 9], ![459, 180, 18]]
    hw := by decide
    g := ![![![-42526, 1030552, 260296], ![95607, -2342656, 0]], ![![2324, -56359, -14235], ![-5219, 128114, 0]]]
    h := ![![![3618, -452, 0], ![51098, 1, 0]], ![![3691, -461, 0], ![52129, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {9} * I113N2 =  Ideal.span {B.equivFun.symm ![50, 14, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E113RS2 
