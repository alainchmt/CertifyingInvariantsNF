import IdealArithmetic.Examples.NF3_1_557179_1.PrimesBelow3_1_557179_1F2
import IdealArithmetic.Examples.NF3_1_557179_1.ClassGroupData3_1_557179_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 8 ![![83, 0, 0], ![-11, 1, 0]]
  ![5111, -464, 385] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![664, 0, 0], ![-88, 8, 0]]
    hsu := by decide
    w := ![![40888, -3712, 3080], ![-55440, 5032, -4176]]
    hw := by decide
    g := ![![![-93, 18, 191], ![9, -165, 0]], ![![3, -2, -11], ![0, 9, 0]]]
    h := ![![![432, 232277, -209080], ![2795, 1928225, 0]], ![![-572, -314945, 283491], ![-3686, -2614475, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {8} * I83N1 =  Ideal.span {B.equivFun.symm ![5111, -464, 385]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E83RS1 


noncomputable def E89RS0 : RelationCertificate Table 48 ![![89, 0, 0], ![-35, 1, 0]]
  ![437, -40, -61] ![![48, 0, 0], ![0, 2, 0]] where
    su := ![![4272, 0, 0], ![-1680, 48, 0]]
    hsu := by decide
    w := ![![20976, -1920, -2928], ![17568, 672, -720]]
    hw := by decide
    g := ![![![-2413, 413860, 3729056], ![17251, -9944634, 0]], ![![1243, 1048879907, 9456309028], ![43703349, -25216823825, 0]]]
    h := ![![![335603, -9584, -2], ![853378, 13, 0]], ![![280524, -8004, -3], ![713322, 28, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {48} * I89N0 =  Ideal.span {B.equivFun.symm ![437, -40, -61]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 16 ![![89, 0, 0], ![-32, 1, 0]]
  ![-159, -16, -1] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![1424, 0, 0], ![-512, 16, 0]]
    hsu := by decide
    w := ![![-2544, -256, -16], ![144, -176, -144]]
    hw := by decide
    g := ![![![110, 270880, 2447542], ![16931, -4351171, 0]], ![![-53, -90765, -820120], ![-5667, 1457984, 0]]]
    h := ![![![-87, -31714, 9208], ![-237, -91057, 0]], ![![17, 1890, -549], ![47, 5428, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {16} * I89N1 =  Ideal.span {B.equivFun.symm ![-159, -16, -1]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 48 ![![89, 0, 0], ![-23, 1, 0]]
  ![97, -8, 7] ![![48, 0, 0], ![0, 2, 0]] where
    su := ![![4272, 0, 0], ![-1104, 48, 0]]
    hsu := by decide
    w := ![![4656, -384, 336], ![-2016, 192, -144]]
    hw := by decide
    g := ![![![7, 194727, 1755586], ![8115, -4681564, 0]], ![![-1, -178752378, -1611564406], ![-7448009, 4297505083, 0]]]
    h := ![![![33172, -1425, -7], ![128357, 70, 0]], ![![-14338, 638, -6], ![-55480, 59, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {48} * I89N2 =  Ideal.span {B.equivFun.symm ![97, -8, 7]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E89RS2 


noncomputable def E101RS1 : RelationCertificate Table 96 ![![101, 0, 0], ![-45, 1, 0]]
  ![203, -80, -75] ![![96, 0, 0], ![0, 2, 0]] where
    su := ![![9696, 0, 0], ![-4320, 96, 0]]
    hsu := by decide
    w := ![![19488, -7680, -7200], ![21600, 96, -1440]]
    hw := by decide
    g := ![![![-1058, 203, 885], ![11, -5145, 0]], ![![585, -100, -372], ![32, 2219, 0]]]
    h := ![![![581668, -12901, -6], ![1305517, 59, 0]], ![![641970, -14252, -3], ![1440861, 32, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {96} * I101N1 =  Ideal.span {B.equivFun.symm ![203, -80, -75]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 2 ![![103, 0, 0], ![25, 1, 0]]
  ![-15, 0, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![206, 0, 0], ![50, 2, 0]]
    hsu := by decide
    w := ![![-30, 0, 2], ![-144, -14, 0]]
    hw := by decide
    g := ![![![-49, -24822, -279278], ![-12409, 62061, 0]], ![![-7, -6083, -68432], ![-3040, 15207, 0]]]
    h := ![![![-130, -11, -2], ![535, 23, 0]], ![![-574, -49, -9], ![2362, 103, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {2} * I103N1 =  Ideal.span {B.equivFun.symm ![-15, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 2 ![![107, 0, 0], ![-39, 1, 0]]
  ![7, 2, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![214, 0, 0], ![-78, 2, 0]]
    hsu := by decide
    w := ![![14, 4, 2], ![-144, 10, 18]]
    hw := by decide
    g := ![![![-83, -24077, -270938], ![-12038, 60207, 0]], ![![39, 8537, 96078], ![4269, -21350, 0]]]
    h := ![![![128, 1, -1], ![351, 12, 0]], ![![-726, 57, -9], ![-1990, 108, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {2} * I107N1 =  Ideal.span {B.equivFun.symm ![7, 2, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 4 ![![109, 0, 0], ![47, 1, 0]]
  ![-41, 4, -3] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![436, 0, 0], ![188, 4, 0]]
    hsu := by decide
    w := ![![-164, 16, -12], ![432, -40, 36]]
    hw := by decide
    g := ![![![7, -56975, -544812], ![-14243, 242138, 0]], ![![5, 4541497, 43428075], ![1135377, -19301367, 0]]]
    h := ![![![-6636, -205, -12], ![15389, 145, 0]], ![![17416, 418, 9], ![-40388, -108, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {4} * I109N0 =  Ideal.span {B.equivFun.symm ![-41, 4, -3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 96 ![![109, 0, 0], ![-44, 1, 0]]
  ![103, 0, -7] ![![96, 0, 0], ![0, 2, 0]] where
    su := ![![10464, 0, 0], ![-4224, 96, 0]]
    hsu := by decide
    w := ![![9888, 0, -672], ![2016, 192, 0]]
    hw := by decide
    g := ![![![12, 2980838, 26839199], ![62117, -143142390, 0]], ![![-6, 23773505, 214054412], ![495318, -1141623533, 0]]]
    h := ![![![573283, -14329, 272], ![1420176, -3295, 0]], ![![116865, -2914, 54], ![289506, -654, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {96} * I109N1 =  Ideal.span {B.equivFun.symm ![103, 0, -7]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 96 ![![109, 0, 0], ![-4, 1, 0]]
  ![-4583, 416, -345] ![![96, 0, 0], ![0, 2, 0]] where
    su := ![![10464, 0, 0], ![-384, 96, 0]]
    hsu := by decide
    w := ![![-439968, 39936, -33120], ![99360, -9024, 7488]]
    hw := by decide
    g := ![![![-14, -95, -828], ![17, 4410, 0]], ![![2, 1771491, 15950343], ![36926, -85068497, 0]]]
    h := ![![![-1779327, 445155, -993], ![-48485515, 11988, 0]], ![![401835, -100531, 222], ![10949745, -2680, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {96} * I109N2 =  Ideal.span {B.equivFun.symm ![-4583, 416, -345]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E109RS2 


noncomputable def E113RS1 : RelationCertificate Table 24 ![![113, 0, 0], ![44, 1, 0]]
  ![-57, -4, 1] ![![24, 0, 0], ![0, 2, 0]] where
    su := ![![2712, 0, 0], ![1056, 24, 0]]
    hsu := by decide
    w := ![![-1368, -96, 24], ![-288, -120, -72]]
    hw := by decide
    g := ![![![55, -7, -10], ![4, 19, 0]], ![![16, -3, -7], ![7, 11, 0]]]
    h := ![![![6119, 104, -7], ![-15716, 88, 0]], ![![1228, -2, -6], ![-3154, 75, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {24} * I113N1 =  Ideal.span {B.equivFun.symm ![-57, -4, 1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E113RS1 


noncomputable def E127RS1 : RelationCertificate Table 8 ![![127, 0, 0], ![33, 1, 0]]
  ![-447, -32, 7] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![1016, 0, 0], ![264, 8, 0]]
    hsu := by decide
    w := ![![-3576, -256, 56], ![-1008, -472, -288]]
    hw := by decide
    g := ![![![2597, 326767, 2989180], ![40853, -2656875, 0]], ![![453, 90959, 831831], ![11374, -739375, 0]]]
    h := ![![![-78345, -2620, -65], ![301496, 918, 0]], ![![-22164, -739, -18], ![85294, 250, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {8} * I127N1 =  Ideal.span {B.equivFun.symm ![-447, -32, 7]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 16 ![![131, 0, 0], ![61, 1, 0]]
  ![31, 0, 1] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![2096, 0, 0], ![976, 16, 0]]
    hsu := by decide
    w := ![![496, 0, 16], ![-144, 32, 0]]
    hw := by decide
    g := ![![![4, -110, -989], ![1, 1758, 0]], ![![2, -113, -1021], ![-7, 1815, 0]]]
    h := ![![![-9499, -204, -7], ![20400, 102, 0]], ![![2683, -18, -9], ![-5762, 131, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {16} * I131N1 =  Ideal.span {B.equivFun.symm ![31, 0, 1]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E131RS1 


noncomputable def E137RS0 : RelationCertificate Table 32 ![![137, 0, 0], ![-54, 1, 0]]
  ![21679, -1968, 1633] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![4384, 0, 0], ![-1728, 32, 0]]
    hsu := by decide
    w := ![![693728, -62976, 52256], ![111712, -10144, 8416]]
    hw := by decide
    g := ![![![214, -21765, -11528], ![-555, 40997, 0]], ![![-101, 8478, 4491], ![247, -15972, 0]]]
    h := ![![![19207313, -356333, 119], ![48729263, -1630, 0]], ![![3092989, -57380, 19], ![7846963, -260, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {32} * I137N0 =  Ideal.span {B.equivFun.symm ![21679, -1968, 1633]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 4 ![![137, 0, 0], ![-30, 1, 0]]
  ![1, 4, 3] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![548, 0, 0], ![-120, 4, 0]]
    hsu := by decide
    w := ![![4, 16, 12], ![-432, 8, 36]]
    hw := by decide
    g := ![![![101, -119042, -1138245], ![-29759, 505890, 0]], ![![-30, -7886061, -75410478], ![-1971512, 33515767, 0]]]
    h := ![![![53, 8, -3], ![242, 46, 0]], ![![-1104, 66, -9], ![-5038, 138, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {4} * I137N1 =  Ideal.span {B.equivFun.symm ![1, 4, 3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E137RS1 
