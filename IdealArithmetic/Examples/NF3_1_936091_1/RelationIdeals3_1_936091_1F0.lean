import IdealArithmetic.Examples.NF3_1_936091_1.PrimesBelow3_1_936091_1F0
import IdealArithmetic.Examples.NF3_1_936091_1.ClassGroupData3_1_936091_1

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

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 4 ![![2, 0, 0], ![-11, 1, 1]]
  ![-4579, 1117, -151] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![8, 0, 0], ![-44, 4, 4]]
    hsu := by decide
    w := ![![-18316, 4468, -604], ![20136, -4912, 664]]
    hw := by decide
    g := ![![![-16, 2, 0], ![-7, 3, 0]], ![![-163, -34, -1], ![-90, -16, 0]]]
    h := ![![![-62, 356, -278], ![405, 0, 0]], ![![75, -392, 305], ![-444, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {4} * I2N1 =  Ideal.span {B.equivFun.symm ![-4579, 1117, -151]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0], ![-11, 0, 1]]
  ![-83, 51, 10] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![27, 0, 0], ![-99, 0, 9]]
    hsu := by decide
    w := ![![-747, 459, 90], ![-2106, 189, 81]]
    hw := by decide
    g := ![![![295, -1229, -575], ![-69, 5258, 0]], ![![2575, 3514, 2243], ![967, -19359, 0]]]
    h := ![![![9, 17, 0], ![10, 0, 0]], ![![-1, 7, -4], ![21, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![-83, 51, 10]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![3, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![2, 1, -2], ![3, 6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![2, 1, -2], ![3, 6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 36 ![![7, 0, 0], ![-11, 2, 1]]
  ![10235, -249, -289] ![![36, 0, 0], ![2, 1, 0]] where
    su := ![![252, 0, 0], ![-396, 72, 36]]
    hsu := by decide
    w := ![![368460, -8964, -10404], ![76536, 4824, -1116]]
    hw := by decide
    g := ![![![-73271269, 47622701910, 23829666509], ![1318782240, -857868000959, 0]], ![![116349517, -75636050355, -37847118096], ![-2094537527, 1362496235217, 0]]]
    h := ![![![447, 149, 51], ![-646, 0, 0]], ![![101, 56, 14], ![-129, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {36} * I7N0 =  Ideal.span {B.equivFun.symm ![10235, -249, -289]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 6 ![![7, 0, 0], ![-3, 1, 0]]
  ![-274529, 66969, -9053] ![![6, 0, 0], ![2, 1, 0]] where
    su := ![![42, 0, 0], ![-18, 6, 0]]
    hsu := by decide
    w := ![![-1647174, 401814, -54318], ![1207224, -294492, 39810]]
    hw := by decide
    g := ![![![545593239, -10911871168, -5592333966], ![-1636780780, 33554003827, 0]], ![![-311767733, 6235354782, 3195619336], ![935303225, -19173716044, 0]]]
    h := ![![![-5806433, 2169748, -80552], ![-13456834, 554811, 0]], ![![4255578, -1590221, 59036], ![9862614, -406617, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {6} * I7N1 =  Ideal.span {B.equivFun.symm ![-274529, 66969, -9053]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![1, 1, 0]]
  ![551, -93, -28] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![33, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![1653, -279, -84], ![4881, 168, -93]]
    hw := by decide
    g := ![![![-39933, 5590, -1157], ![15176, -980, 0]], ![![19571, -2978, 826], ![-7516, -294, 0]]]
    h := ![![![98, 39, -3], ![-527, 5, 0]], ![![145, 145, 140], ![32, -1571, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![551, -93, -28]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 36 ![![11, 0, 0], ![3, 1, 0]]
  ![1241, -303, 41] ![![36, 0, 0], ![2, 1, 0]] where
    su := ![![396, 0, 0], ![108, 36, 0]]
    hsu := by decide
    w := ![![44676, -10908, 1476], ![-5472, 1332, -180]]
    hw := by decide
    g := ![![![-3, 25, 13], ![15, -470, 0]], ![![-1, 13, 7], ![25, -255, 0]]]
    h := ![![![1189, 362, 14], ![-3946, -113, 0]], ![![-148, -46, -2], ![492, 17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {36} * I11N1 =  Ideal.span {B.equivFun.symm ![1241, -303, 41]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 2 ![![11, 0, 0], ![-5, 1, 0]]
  ![455, -111, 15] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![22, 0, 0], ![-10, 2, 0]]
    hsu := by decide
    w := ![![910, -222, 30], ![-2910, 710, -96]]
    hw := by decide
    g := ![![![-23, 4, 18], ![4, -33, 0]], ![![-16, -2, -9], ![-1, 18, 0]]]
    h := ![![![4795, -1099, 29], ![10458, -304, 0]], ![![-15325, 3519, -94], ![-33424, 986, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {2} * I11N2 =  Ideal.span {B.equivFun.symm ![455, -111, 15]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 18 ![![13, 0, 0], ![4, 1, 0]]
  ![-6929, -309, 121] ![![18, 0, 0], ![2, 1, 0]] where
    su := ![![234, 0, 0], ![72, 18, 0]]
    hsu := by decide
    w := ![![-124722, -5562, 2178], ![-37332, -5490, 54]]
    hw := by decide
    g := ![![![-59965, 14985, -2061], ![-5825, 1120, 0]], ![![11058, -2828, 348], ![1080, 371, 0]]]
    h := ![![![-282057, -80998, -2639], ![914953, 34428, 0]], ![![-85074, -24421, -792], ![275972, 10299, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {18} * I13N0 =  Ideal.span {B.equivFun.symm ![-6929, -309, 121]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS0 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![-6, 1, 0]]
  ![-2677, -41, 59] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![68, 0, 0], ![-24, 4, 0]]
    hsu := by decide
    w := ![![-10708, -164, 236], ![-16800, -1756, 136]]
    hw := by decide
    g := ![![![154721, -60887, 6112], ![62141, 59, 0]], ![![-112832, 44391, -4463], ![-45317, -20, 0]]]
    h := ![![![-4415, 764, -6], ![-12063, 161, 0]], ![![-6912, 1175, -13], ![-18884, 255, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![-2677, -41, 59]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 9 ![![19, 0, 0], ![1, 1, 0]]
  ![59, -15, 2] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![171, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![531, -135, 18], ![-270, 63, -9]]
    hw := by decide
    g := ![![![-301, 12498, 6323], ![1328, -56906, 0]], ![![-73, 3040, 1538], ![322, -13842, 0]]]
    h := ![![![6, 2, 0], ![-55, 2, 0]], ![![-2, -2, -2], ![8, 37, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {9} * I19N0 =  Ideal.span {B.equivFun.symm ![59, -15, 2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 6 ![![19, 0, 0], ![3, 1, 0]]
  ![55, 15, 1] ![![6, 0, 0], ![2, 1, 0]] where
    su := ![![114, 0, 0], ![18, 6, 0]]
    hsu := by decide
    w := ![![330, 90, 6], ![-84, 102, 18]]
    hw := by decide
    g := ![![![315, -8844, -4558], ![-1369, 27320, 0]], ![![99, -1563, -796], ![-221, 4781, 0]]]
    h := ![![![745, 254, 2], ![-4700, -37, 0]], ![![-188, -65, -1], ![1186, 22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {6} * I19N1 =  Ideal.span {B.equivFun.symm ![55, 15, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 4 ![![19, 0, 0], ![-5, 1, 0]]
  ![29, -7, 1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![76, 0, 0], ![-20, 4, 0]]
    hsu := by decide
    w := ![![116, -28, 4], ![-136, 32, -4]]
    hw := by decide
    g := ![![![-586689, 5866915, 3080131], ![1173386, -12320525, 0]], ![![185243, -1852431, -972526], ![-370483, 3890104, 0]]]
    h := ![![![51, -10, 0], ![188, 1, 0]], ![![-46, 14, -1], ![-168, 18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {4} * I19N2 =  Ideal.span {B.equivFun.symm ![29, -7, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E19RS2 


noncomputable def E23RS0 : RelationCertificate Table 2 ![![23, 0, 0], ![10, 1, 0]]
  ![-1471, -569, -53] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![46, 0, 0], ![20, 2, 0]]
    hsu := by decide
    w := ![![-2942, -1138, -106], ![10282, -2372, -622]]
    hw := by decide
    g := ![![![1730036, -337622, 59007], ![-168811, -3913, 0]], ![![270981, -52883, 9846], ![-26441, -1820, 0]]]
    h := ![![![-3587, -454, -10], ![8103, 177, 0]], ![![12197, 1401, 12], ![-27539, -587, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {2} * I23N0 =  Ideal.span {B.equivFun.symm ![-1471, -569, -53]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 3 ![![23, 0, 0], ![-8, 1, 0]]
  ![41, 0, -1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![69, 0, 0], ![-24, 3, 0]]
    hsu := by decide
    w := ![![123, 0, -3], ![153, 24, 0]]
    hw := by decide
    g := ![![![71, -22, 15], ![-30, -37, 0]], ![![-44, 9, -5], ![20, 10, 0]]]
    h := ![![![71, -9, 0], ![199, -1, 0]], ![![93, -11, 0], ![261, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {3} * I23N1 =  Ideal.span {B.equivFun.symm ![41, 0, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 36 ![![23, 0, 0], ![-3, 1, 0]]
  ![-3623, -867, -47] ![![36, 0, 0], ![2, 1, 0]] where
    su := ![![828, 0, 0], ![-108, 36, 0]]
    hsu := by decide
    w := ![![-130428, -31212, -1692], ![1872, -6156, -1008]]
    hw := by decide
    g := ![![![-13643, 3359, -449], ![-647, -75, 0]], ![![5601, -19760, -9017], ![-216, 331247, 0]]]
    h := ![![![-4549, 1450, -10], ![-33668, 183, 0]], ![![68, -27, -2], ![504, 18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {36} * I23N2 =  Ideal.span {B.equivFun.symm ![-3623, -867, -47]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E23RS2 


noncomputable def E29RS0 : RelationCertificate Table 36 ![![29, 0, 0], ![-13, 1, 0]]
  ![23889359, -5827605, 787787] ![![36, 0, 0], ![2, 1, 0]] where
    su := ![![1044, 0, 0], ![-468, 36, 0]]
    hsu := by decide
    w := ![![860016924, -209793780, 28360332], ![-105051960, 25626528, -3464244]]
    hw := by decide
    g := ![![![-1531758178379, 995642815483722, 498204347286262], ![27571647198006, -17935356502304263, 0]], ![![739469465137, -480655152273497, -240512443502993], ![-13310450370631, 8658447966107384, 0]]]
    h := ![![![147101994, -12658495, 119886], ![326312959, -2688907, 0]], ![![-17968652, 1546258, -14645], ![-39859446, 328476, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {36} * I29N0 =  Ideal.span {B.equivFun.symm ![23889359, -5827605, 787787]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 36 ![![29, 0, 0], ![-4, 1, 0]]
  ![25, -3, 1] ![![36, 0, 0], ![2, 1, 0]] where
    su := ![![1044, 0, 0], ![-144, 36, 0]]
    hsu := by decide
    w := ![![900, -108, 36], ![-144, 36, 0]]
    hw := by decide
    g := ![![![773, -502648, -251517], ![-13897, 9054611, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![3817, -970, 4], ![27667, -115, 0]], ![![-604, 155, -1], ![-4378, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {36} * I29N1 =  Ideal.span {B.equivFun.symm ![25, -3, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS1 
