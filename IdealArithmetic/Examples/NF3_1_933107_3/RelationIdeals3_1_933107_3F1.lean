import IdealArithmetic.Examples.NF3_1_933107_3.PrimesBelow3_1_933107_3F1
import IdealArithmetic.Examples.NF3_1_933107_3.ClassGroupData3_1_933107_3

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 50 ![![41, 0, 0], ![9, 1, 0]]
  ![507, -1, 16] ![![50, 0, 0], ![12, 1, 0]] where
    su := ![![2050, 0, 0], ![450, 50, 0]]
    hsu := by decide
    w := ![![25350, -50, 800], ![6450, 0, 200]]
    hw := by decide
    g := ![![![788710, 5077564, 3615412], ![290867, -22782830, 114772]], ![![225337, 1450728, 1032972], ![83138, -6509362, 32792]]]
    h := ![![![1506701, 6443275, 6455176], ![487924, -33082775, 0]], ![![383337, 1639312, 1642340], ![124144, -8416992, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {50} * I41N1 =  Ideal.span {B.equivFun.symm ![507, -1, 16]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E41RS1 


noncomputable def E43RS0 : RelationCertificate Table 20 ![![43, 0, 0], ![19, 1, 0]]
  ![-1117, 1, -36] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![860, 0, 0], ![380, 20, 0]]
    hsu := by decide
    w := ![![-22340, 20, -720], ![-3060, 0, -100]]
    hw := by decide
    g := ![![![-993670, -496930, -4024559], ![-124201, 10061415, -45]], ![![-445029, -222557, -1802452], ![-55618, 4506138, -20]]]
    h := ![![![-8077, -95255, -42396], ![-5766, 227874, 0]], ![![-1123, -13048, -5807], ![-752, 31212, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {20} * I43N0 =  Ideal.span {B.equivFun.symm ![-1117, 1, -36]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 50 ![![43, 0, 0], ![-10, 1, 0]]
  ![29, 3, 2] ![![50, 0, 0], ![12, 1, 0]] where
    su := ![![2150, 0, 0], ![-500, 50, 0]]
    hsu := by decide
    w := ![![1450, 150, 100], ![400, 0, 50]]
    hw := by decide
    g := ![![![-1903970, -11361359, -8272727], ![-684139, 51704614, -43]], ![![532397, 3176928, 2313268], ![191314, -14457943, 11]]]
    h := ![![![79073, -471732, 343574], ![-29331, -1846710, 0]], ![![21896, -130584, 95107], ![-8088, -511200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {50} * I43N1 =  Ideal.span {B.equivFun.symm ![29, 3, 2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![-6, 1, 0]]
  ![-5, 7, 2] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![94, 0, 0], ![-12, 2, 0]]
    hsu := by decide
    w := ![![-10, 14, 4], ![60, -74, 58]]
    hw := by decide
    g := ![![![-157002, 173906, -6874], ![86954, 0, 14025]], ![![18875, -20869, 826], ![-10434, 0, -1683]]]
    h := ![![![-175, 631, -722], ![44, 4242, 0]], ![![1056, -3772, 4315], ![-182, -25347, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![-5, 7, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS1 


noncomputable def E59RS1 : RelationCertificate Table 4 ![![59, 0, 0], ![3, 1, 0]]
  ![3, 1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![236, 0, 0], ![12, 4, 0]]
    hsu := by decide
    w := ![![12, 4, 0], ![8, 4, 8]]
    hw := by decide
    g := ![![![1190010, -1749537, 165497], ![157625, 0, -220662]], ![![61026, -89720, 8487], ![8084, 0, -11316]]]
    h := ![![![-28, -28, -112], ![1, 826, 0]], ![![-20, -19, -74], ![30, 546, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {4} * I59N1 =  Ideal.span {B.equivFun.symm ![3, 1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![24, 1, 0]]
  ![-10521, 11, -340] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![122, 0, 0], ![48, 2, 0]]
    hsu := by decide
    w := ![![-21042, 22, -680], ![-7798, 8, -252]]
    hw := by decide
    g := ![![![318576, -343507, 13864], ![-171753, 0, -27702]], ![![128553, -138614, 5594], ![-69305, 0, -11178]]]
    h := ![![![758783, 10877857, 3786316], ![476880, -28870702, 0]], ![![281185, 4031245, 1403178], ![176763, -10699248, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![-10521, 11, -340]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 10 ![![67, 0, 0], ![-7, 1, 0]]
  ![1, -3, -2] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![670, 0, 0], ![-70, 10, 0]]
    hsu := by decide
    w := ![![10, -30, -20], ![-50, 60, -30]]
    hw := by decide
    g := ![![![3854777, 2194886, 16771822], ![990444, -20988380, 62933]], ![![-328066, -186799, -1427389], ![-84291, 1786245, -5356]]]
    h := ![![![-416, 1716, -1718], ![129, 14388, 0]], ![![1944, -7883, 7887], ![-265, -66054, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {10} * I67N1 =  Ideal.span {B.equivFun.symm ![1, -3, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 50 ![![71, 0, 0], ![-31, 1, 0]]
  ![-21, 3, 2] ![![50, 0, 0], ![12, 1, 0]] where
    su := ![![3550, 0, 0], ![-1550, 50, 0]]
    hsu := by decide
    w := ![![-1050, 150, 100], ![-200, -50, 50]]
    hw := by decide
    g := ![![![-20020529, -121141340, -87839511], ![-7227720, 549839062, -518227]], ![![8227599, 49784104, 36098424], ![2970356, -225961226, 212970]]]
    h := ![![![100, -1528, 382], ![11, -3390, 0]], ![![19, -284, 71], ![3, -630, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {50} * I71N1 =  Ideal.span {B.equivFun.symm ![-21, 3, 2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 4 ![![73, 0, 0], ![-5, 1, 0]]
  ![-5, 1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![292, 0, 0], ![-20, 4, 0]]
    hsu := by decide
    w := ![![-20, 4, 0], ![-8, -4, 8]]
    hw := by decide
    g := ![![![-1363, 1983, -188], ![-183, 0, 250]], ![![87, -127, 12], ![12, 0, -16]]]
    h := ![![![32, -96, 128], ![1, -1168, 0]], ![![15, -38, 50], ![37, -456, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {4} * I73N1 =  Ideal.span {B.equivFun.symm ![-5, 1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![-2, 1, 0]]
  ![-1, 1, -2] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-2, 2, -4], ![-44, 60, 6]]
    hw := by decide
    g := ![![![1752, -2938, 87], ![-1469, 0, -237]], ![![-88, 111, -4], ![57, 0, 9]]]
    h := ![![![-39, 59, -158], ![20, 1560, 0]], ![![-876, 1315, -3507], ![41, 34632, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![-1, 1, -2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS1 
