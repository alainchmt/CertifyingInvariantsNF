import IdealArithmetic.Examples.NF3_1_692259_1.PrimesBelow3_1_692259_1F1
import IdealArithmetic.Examples.NF3_1_692259_1.ClassGroupData3_1_692259_1

set_option linter.all false

noncomputable section


noncomputable def E43RS0 : RelationCertificate Table 4 ![![43, 0, 0], ![11, 1, 0]]
  ![28, 2, 1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![172, 0, 0], ![44, 4, 0]]
    hsu := by decide
    w := ![![112, 8, 4], ![180, 12, 8]]
    hw := by decide
    g := ![![![-5145926, 302700, 16345891], ![-1210804, -21794521, 0]], ![![-1196828, 70401, 3801693], ![-281605, -5068924, 0]]]
    h := ![![![-435, 4323, 1297], ![13, -18590, 0]], ![![-701, 6956, 2087], ![25, -29913, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {4} * I43N0 =  Ideal.span {B.equivFun.symm ![28, 2, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS0 


noncomputable def E43RS2 : RelationCertificate Table 2 ![![43, 0, 0], ![17, 1, 0]]
  ![-4214704, -249696, -158409] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![86, 0, 0], ![34, 2, 0]]
    hsu := by decide
    w := ![![-8429408, -499392, -316818], ![-28359994, -1680160, -1065906]]
    hw := by decide
    g := ![![![1162, -805, 216], ![179, 0, 0]], ![![1125, -479, 36], ![323, 3, 0]]]
    h := ![![![-302604015, 4879223153, 914824869], ![-6163803, -13112542592, 0]], ![![-1018084278, 16415712629, 3077846961], ![-20737655, -44115984092, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {2} * I43N2 =  Ideal.span {B.equivFun.symm ![-4214704, -249696, -158409]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS2 


noncomputable def E53RS1 : RelationCertificate Table 4 ![![53, 0, 0], ![15, 1, 0]]
  ![53476420, 3168158, 2009903] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![212, 0, 0], ![60, 4, 0]]
    hsu := by decide
    w := ![![213905680, 12672632, 8039612], ![359833324, 21317972, 13524280]]
    hw := by decide
    g := ![![![-15488239797577, 911072927905, 49197938206843], ![-3644291717416, -65597250942497, 0]], ![![-4091233153946, 240660773564, 12995681790272], ![-962643095095, -17327575720484, 0]]]
    h := ![![![692803250, -9734455534, -2085879479], ![12407440, 36851207430, 0]], ![![1165437482, -16375355213, -3508878055], ![20871852, 61991305995, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {4} * I53N1 =  Ideal.span {B.equivFun.symm ![53476420, 3168158, 2009903]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 4 ![![59, 0, 0], ![-28, 1, 0]]
  ![-71332, -4226, -2681] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![236, 0, 0], ![-112, 4, 0]]
    hsu := by decide
    w := ![![-285328, -16904, -10724], ![-479980, -28436, -18040]]
    hw := by decide
    g := ![![![5203439323, -306084607, -16528572763], ![1224338680, 22038097007, 0]], ![![-2557622581, 150448355, 8124213219], ![-601793553, -10832284283, 0]]]
    h := ![![![10692348, 308081574, -31870819], ![147428, 626791880, 0]], ![![17986699, 518256161, -53613230], ![247972, 1054392020, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {4} * I59N1 =  Ideal.span {B.equivFun.symm ![-71332, -4226, -2681]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![-26, 1, 0]]
  ![159178, 24052, -22527] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![122, 0, 0], ![-52, 2, 0]]
    hsu := by decide
    w := ![![318356, 48104, -45054], ![-3334032, 519610, 27102]]
    hw := by decide
    g := ![![![-67684054427, 9641171889, -3089277669], ![-29021441267, -183, 0]], ![![22492385237, -3203900153, 1026611397], ![9644242543, 78, 0]]]
    h := ![![![2141566, 57422767, -6380685], ![28587, 129733086, 0]], ![![-23431837, -628312093, 69813720], ![-312843, -1419541123, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![159178, 24052, -22527]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 2 ![![67, 0, 0], ![10, 1, 0]]
  ![-26973930, -1598044, -1013811] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![134, 0, 0], ![20, 2, 0]]
    hsu := by decide
    w := ![![-53947860, -3196088, -2027622], ![-181502780, -10752954, -6821754]]
    hw := by decide
    g := ![![![12338, -3793, -672], ![4273, 201, 0]], ![![1097, -156, -180], ![473, 30, 0]]]
    h := ![![![112748138, -1020548270, -340181997], ![1596082, 7597059996, 0]], ![![379331114, -3433543944, -1144512093], ![5369709, 25559633118, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {2} * I67N1 =  Ideal.span {B.equivFun.symm ![-26973930, -1598044, -1013811]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 2 ![![71, 0, 0], ![27, 1, 0]]
  ![-8758, 178, 587] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![142, 0, 0], ![54, 2, 0]]
    hsu := by decide
    w := ![![-17516, 356, 1174], ![81462, -18150, 1708]]
    hw := by decide
    g := ![![![60020965, -8549608, 2739838], ![25735680, -213, 0]], ![![27667832, -3941109, 1262951], ![11863363, -78, 0]]]
    h := ![![![-86087, 2245939, 259153], ![-1099, -6133092, 0]], ![![401976, -10487630, -1210076], ![5155, 28638750, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {2} * I71N1 =  Ideal.span {B.equivFun.symm ![-8758, 178, 587]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS1 


noncomputable def E73RS0 : RelationCertificate Table 2 ![![73, 0, 0], ![-35, 1, 0]]
  ![6977394, -1572846, 154229] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![146, 0, 0], ![-70, 2, 0]]
    hsu := by decide
    w := ![![13954788, -3145692, 308458], ![32301506, 4509730, -4410080]]
    hw := by decide
    g := ![![![-34183208536991, 4869185096672, -1560211385206], ![-14657011720158, 219, 0]], ![![13706613337225, -1952421678475, 625605819280], ![5877095829375, -108, 0]]]
    h := ![![![48556368, 1735937928, -144661747], ![499530, 3520153920, 0]], ![![110771251, 3960152971, -330041680], ![1139182, 8030279200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {2} * I73N0 =  Ideal.span {B.equivFun.symm ![6977394, -1572846, 154229]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS0 


noncomputable def E73RS1 : RelationCertificate Table 2 ![![73, 0, 0], ![-3, 1, 0]]
  ![-63326, -3312, 6243] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![146, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![-126652, -6624, 12486], ![901408, -163214, 2550]]
    hw := by decide
    g := ![![![5534844757, -788404149, 252625179], ![2373220305, -219, 0]], ![![206898739, -29471437, 9443388], ![88713652, 9, 0]]]
    h := ![![![227779, 913973, -685461], ![3187, 16681632, 0]], ![![-1636998, -6569768, 4926738], ![-22675, -119883533, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2} * I73N1 =  Ideal.span {B.equivFun.symm ![-63326, -3312, 6243]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 
