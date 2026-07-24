import IdealArithmetic.Examples.NF3_1_936684_4.PrimesBelow3_1_936684_4F2
import IdealArithmetic.Examples.NF3_1_936684_4.ClassGroupData3_1_936684_4

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 10 ![![83, 0, 0], ![-39, 1, 0]]
  ![290, 97, 9] ![![10, 0, 0], ![-52, -4, 1]] where
    su := ![![830, 0, 0], ![-390, 10, 0]]
    hsu := by decide
    w := ![![2900, 970, 90], ![6270, 2070, 190]]
    hw := by decide
    g := ![![![1879507, 934300, 388626], ![-10108261, -1555500, 0]], ![![-882068, -438495, -182396], ![4744153, 730048, 0]]]
    h := ![![![127978, -3783, 13], ![272356, -1070, 0]], ![![276612, -8173, 28], ![588671, -2305, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {10} * I83N1 =  Ideal.span {B.equivFun.symm ![290, 97, 9]} * (J0 ^ 0*J1^ 1*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1J2_2 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 50 ![![89, 0, 0], ![1, 1, 0]]
  ![-250, -79, -7] ![![50, 0, 0], ![-46, -4, 1]] where
    su := ![![4450, 0, 0], ![50, 50, 0]]
    hsu := by decide
    w := ![![-12500, -3950, -350], ![-6350, -2100, -200]]
    hw := by decide
    g := ![![![-15082, -1916, 39], ![14043, 4002, 0]], ![![-279, -37, 0], ![337, 84, 0]]]
    h := ![![![-3, -3, -2], ![17, 171, 0]], ![![-2, -2, -1], ![51, 85, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {50} * I89N1 =  Ideal.span {B.equivFun.symm ![-250, -79, -7]} * (J0 ^ 2*J1^ 0*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0J2_2 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 10 ![![97, 0, 0], ![13, 1, 0]]
  ![90, 31, 3] ![![10, 0, 0], ![-56, -4, 1]] where
    su := ![![970, 0, 0], ![130, 10, 0]]
    hsu := by decide
    w := ![![900, 310, 30], ![1610, 550, 50]]
    hw := by decide
    g := ![![![309, 102, 53], ![-1583, -260, 0]], ![![43, 15, 8], ![-237, -39, 0]]]
    h := ![![![158, 12, 0], ![-1172, 3, 0]], ![![302, 23, 0], ![-2241, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {10} * I97N1 =  Ideal.span {B.equivFun.symm ![90, 31, 3]} * (J0 ^ 1*J1^ 0*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0J2_2 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 25 ![![101, 0, 0], ![-46, 1, 0]]
  ![-25, -19, 2] ![![25, 0, 0], ![-3, 1, 0]] where
    su := ![![2525, 0, 0], ![-1150, 25, 0]]
    hsu := by decide
    w := ![![-625, -475, 50], ![775, 200, -25]]
    hw := by decide
    g := ![![![17, 2371, -791], ![96, 19778, 0]], ![![-7, -1076, 359], ![-41, -8976, 0]]]
    h := ![![![-151, 4, 0], ![-331, 2, 0]], ![![305, -7, 0], ![669, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {25} * I101N1 =  Ideal.span {B.equivFun.symm ![-25, -19, 2]} * (J0 ^ 0*J1^ 2*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2J2_0 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 25 ![![103, 0, 0], ![37, 1, 0]]
  ![-75, -4, 1] ![![25, 0, 0], ![-59, 0, 1]] where
    su := ![![2575, 0, 0], ![925, 25, 0]]
    hsu := by decide
    w := ![![-1875, -100, 25], ![3025, 250, -50]]
    hw := by decide
    g := ![![![37, -2, -1], ![18, 0, 0]], ![![49, -1, -1], ![22, 0, 0]]]
    h := ![![![-800, -59, -1], ![2225, 104, 0]], ![![1266, 35, 0], ![-3521, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {25} * I103N1 =  Ideal.span {B.equivFun.symm ![-75, -4, 1]} * (J0 ^ 2*J1^ 2*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2J2_0 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 50 ![![107, 0, 0], ![12, 1, 0]]
  ![-500, -29, 7] ![![50, 0, 0], ![-72, -4, 1]] where
    su := ![![5350, 0, 0], ![600, 50, 0]]
    hsu := by decide
    w := ![![-25000, -1450, 350], ![16050, 1750, -300]]
    hw := by decide
    g := ![![![-47241, 467, 299], ![68067, 20752, 0]], ![![-5591, 59, 35], ![8172, 2480, 0]]]
    h := ![![![-508, -43, 0], ![4488, 7, 0]], ![![303, 14, -1], ![-2675, 101, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {50} * I107N0 =  Ideal.span {B.equivFun.symm ![-500, -29, 7]} * (J0 ^ 0*J1^ 2*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2J2_2 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 50 ![![107, 0, 0], ![40, 1, 0]]
  ![200, 71, 7] ![![50, 0, 0], ![-72, -4, 1]] where
    su := ![![5350, 0, 0], ![2000, 50, 0]]
    hsu := by decide
    w := ![![10000, 3550, 350], ![650, 150, 0]]
    hw := by decide
    g := ![![![3763, -35, -24], ![-5411, -1648, 0]], ![![1512, -11, -10], ![-2070, -641, 0]]]
    h := ![![![157800, 5143, 30], ![-422110, -3203, 0]], ![![10199, 295, 1], ![-27282, -107, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {50} * I107N1 =  Ideal.span {B.equivFun.symm ![200, 71, 7]} * (J0 ^ 0*J1^ 2*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2J2_2 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 50 ![![107, 0, 0], ![-52, 1, 0]]
  ![-100, -37, -4] ![![50, 0, 0], ![-72, -4, 1]] where
    su := ![![5350, 0, 0], ![-2600, 50, 0]]
    hsu := by decide
    w := ![![-5000, -1850, -200], ![-150, -100, 0]]
    hw := by decide
    g := ![![![-16284, 160, 103], ![23481, 7154, 0]], ![![7817, -72, -50], ![-11116, -3402, 0]]]
    h := ![![![-2564, 99, -1], ![-5274, 103, 0]], ![![-53, 53, -1], ![-109, 107, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {50} * I107N2 =  Ideal.span {B.equivFun.symm ![-100, -37, -4]} * (J0 ^ 0*J1^ 2*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2J2_2 E107RS2 


noncomputable def E109RS1 : RelationCertificate Table 50 ![![109, 0, 0], ![-26, 1, 0]]
  ![50, 14, 1] ![![50, 0, 0], ![-506, -25, 9]] where
    su := ![![5450, 0, 0], ![-1300, 50, 0]]
    hsu := by decide
    w := ![![2500, 700, 50], ![10050, 3300, 350]]
    hw := by decide
    g := ![![![57, 1, -1], ![9, 0, 0]], ![![418, 208, 54], ![-576, -99, 0]]]
    h := ![![![374, -14, 0], ![1566, 1, 0]], ![![1387, -51, 0], ![5807, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {50} * I109N1 =  Ideal.span {B.equivFun.symm ![50, 14, 1]} * (J0 ^ 2*J1^ 2*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2J2_1 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 10 ![![113, 0, 0], ![-53, 1, 0]]
  ![-220, -12, 3] ![![10, 0, 0], ![-54, -5, 1]] where
    su := ![![1130, 0, 0], ![-530, 10, 0]]
    hsu := by decide
    w := ![![-2200, -120, 30], ![2430, 530, -70]]
    hw := by decide
    g := ![![![-2478, 269, -276], ![13471, 2147, 0]], ![![1211, -128, 131], ![-6431, -1026, 0]]]
    h := ![![![-5074, 150, -1], ![-10814, 116, 0]], ![![5683, -110, 0], ![12112, -7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {10} * I113N1 =  Ideal.span {B.equivFun.symm ![-220, -12, 3]} * (J0 ^ 1*J1^ 1*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1J2_1 E113RS1 


noncomputable def E127RS0 : RelationCertificate Table 25 ![![127, 0, 0], ![-52, 1, 0]]
  ![75, 24, 2] ![![25, 0, 0], ![-49, -5, 1]] where
    su := ![![3175, 0, 0], ![-1300, 25, 0]]
    hsu := by decide
    w := ![![1875, 600, 50], ![1225, 325, 25]]
    hw := by decide
    g := ![![![12667266, 1166503, 119715], ![-25056327, -4412694, 0]], ![![-4966642, -457368, -46939], ![9824252, 1730157, 0]]]
    h := ![![![1093, -20, 0], ![2668, 2, 0]], ![![703, -13, 0], ![1716, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {25} * I127N0 =  Ideal.span {B.equivFun.symm ![75, 24, 2]} * (J0 ^ 2*J1^ 1*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1J2_0 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 25 ![![127, 0, 0], ![-45, 1, 0]]
  ![125, 43, 4] ![![25, 0, 0], ![-49, -5, 1]] where
    su := ![![3175, 0, 0], ![-1125, 25, 0]]
    hsu := by decide
    w := ![![3125, 1075, 100], ![1925, 600, 50]]
    hw := by decide
    g := ![![![22327220, 2056070, 211008], ![-44164049, -7777770, 0]], ![![-7791718, -717524, -73638], ![15412365, 2714283, 0]]]
    h := ![![![3005, -65, 0], ![8478, 4, 0]], ![![1841, -40, 0], ![5194, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {25} * I127N1 =  Ideal.span {B.equivFun.symm ![125, 43, 4]} * (J0 ^ 2*J1^ 1*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1J2_0 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 25 ![![127, 0, 0], ![-30, 1, 0]]
  ![-25, -8, 1] ![![25, 0, 0], ![-49, -5, 1]] where
    su := ![![3175, 0, 0], ![-750, 25, 0]]
    hsu := by decide
    w := ![![-625, -200, 25], ![-3325, -225, 50]]
    hw := by decide
    g := ![![![1601, 148, 15], ![-3144, -554, 0]], ![![-318, -29, -4], ![710, 122, 0]]]
    h := ![![![-21955, 792, -2], ![-92942, 255, 0]], ![![-116959, 4079, -6], ![-495122, 764, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {25} * I127N2 =  Ideal.span {B.equivFun.symm ![-25, -8, 1]} * (J0 ^ 2*J1^ 1*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1J2_0 E127RS2 


noncomputable def E131RS1 : RelationCertificate Table 5 ![![131, 0, 0], ![-56, 1, 0]]
  ![-135, -9, 2] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![655, 0, 0], ![-280, 5, 0]]
    hsu := by decide
    w := ![![-675, -45, 10], ![430, 15, -5]]
    hw := by decide
    g := ![![![25, -77, -42], ![-4, 213, 0]], ![![-10, 33, 18], ![4, -91, 0]]]
    h := ![![![-38765, 805, -2], ![-90680, 264, 0]], ![![24786, -499, 1], ![57980, -132, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {5} * I131N1 =  Ideal.span {B.equivFun.symm ![-135, -9, 2]} * (J0 ^ 0*J1^ 1*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1J2_0 E131RS1 


noncomputable def E137RS0 : RelationCertificate Table 5 ![![137, 0, 0], ![14, 1, 0]]
  ![-155, -18, 3] ![![5, 0, 0], ![-54, -5, 1]] where
    su := ![![685, 0, 0], ![70, 5, 0]]
    hsu := by decide
    w := ![![-775, -90, 15], ![-3180, 25, 25]]
    hw := by decide
    g := ![![![35, 55, 10], ![-17, 0, 0]], ![![50, 14, 1], ![1, 0, 0]]]
    h := ![![![-737, -67, -1], ![7201, 140, 0]], ![![-2980, -227, -1], ![29116, 142, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {5} * I137N0 =  Ideal.span {B.equivFun.symm ![-155, -18, 3]} * (J0 ^ 1*J1^ 1*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1J2_0 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 25 ![![137, 0, 0], ![31, 1, 0]]
  ![625, 207, 19] ![![25, 0, 0], ![-3, 1, 0]] where
    su := ![![3425, 0, 0], ![775, 25, 0]]
    hsu := by decide
    w := ![![15625, 5175, 475], ![4775, 1600, 150]]
    hw := by decide
    g := ![![![-103109, -21776426, 7270257], ![-858668, -181756399, 0]], ![![-23795, -5026118, 1678015], ![-198184, -41950370, 0]]]
    h := ![![![351507, 12080, 24], ![-1553414, -3269, 0]], ![![107413, 3681, 7], ![-474690, -953, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {25} * I137N1 =  Ideal.span {B.equivFun.symm ![625, 207, 19]} * (J0 ^ 0*J1^ 2*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2J2_0 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 25 ![![137, 0, 0], ![-45, 1, 0]]
  ![-925, -33, 11] ![![25, 0, 0], ![3, 1, 0]] where
    su := ![![3425, 0, 0], ![-1125, 25, 0]]
    hsu := by decide
    w := ![![-23125, -825, 275], ![1075, -100, 0]]
    hw := by decide
    g := ![![![-64, 1580, 532], ![59, -13344, 0]], ![![16, -503, -169], ![-15, 4236, 0]]]
    h := ![![![-26450, 636, -1], ![-80505, 148, 0]], ![![1304, -29, 0], ![3969, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {25} * I137N2 =  Ideal.span {B.equivFun.symm ![-925, -33, 11]} * (J0 ^ 2*J1^ 0*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0J2_0 E137RS2 
