import IdealArithmetic.Examples.NF3_1_703404_2.PrimesBelow3_1_703404_2F2
import IdealArithmetic.Examples.NF3_1_703404_2.ClassGroupData3_1_703404_2

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 98 ![![97, 0, 0], ![-29, 1, 0]]
  ![190, -11, -1] ![![98, 0, 0], ![-28, -4, 1]] where
    su := ![![9506, 0, 0], ![-2842, 98, 0]]
    hsu := by decide
    w := ![![18620, -1078, -98], ![-7154, -1176, 196]]
    hw := by decide
    g := ![![![1445980842, 209985324, -19611242], ![-421908281, -585952498, 0]], ![![-410345902, -59590428, 5565352], ![119730773, 166283817, 0]]]
    h := ![![![570130, -21168, 52], ![1906980, -5045, 0]], ![![-218763, 8153, -21], ![-731722, 2039, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {98} * I97N1 =  Ideal.span {B.equivFun.symm ![190, -11, -1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![-41, 1, 0]]
  ![30, 10, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![202, 0, 0], ![-82, 2, 0]]
    hsu := by decide
    w := ![![60, 20, 2], ![262, 96, 10]]
    hw := by decide
    g := ![![![-1, -8, 1], ![-3, 0, 0]], ![![3, 3, 1], ![3, -3, 0]]]
    h := ![![![2604, -63, 0], ![6414, 1, 0]], ![![11051, -267, 0], ![27220, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![30, 10, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 2 ![![103, 0, 0], ![21, 1, 0]]
  ![-154, -13, 3] ![![2, 0, 0], ![-44, -4, 1]] where
    su := ![![206, 0, 0], ![42, 2, 0]]
    hsu := by decide
    w := ![![-308, -26, 6], ![226, 324, -36]]
    hw := by decide
    g := ![![![50, -128, -31], ![25, 0, 0]], ![![5, -39, -9], ![7, 0, 0]]]
    h := ![![![-3934, -209, -1], ![19288, 106, 0]], ![![2894, 143, 0], ![-14189, -18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {2} * I103N1 =  Ideal.span {B.equivFun.symm ![-154, -13, 3]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E103RS1 


noncomputable def E109RS0 : RelationCertificate Table 14 ![![109, 0, 0], ![39, 1, 0]]
  ![304, 107, 11] ![![14, 0, 0], ![-42, -4, 1]] where
    su := ![![1526, 0, 0], ![546, 14, 0]]
    hsu := by decide
    w := ![![4256, 1498, 154], ![3738, 1330, 140]]
    hw := by decide
    g := ![![![41, -3, 3], ![-113, -22, 0]], ![![25, 0, 1], ![-45, -9, 0]]]
    h := ![![![1366, 32, 0], ![-3810, 11, 0]], ![![1161, 27, 0], ![-3238, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {14} * I109N0 =  Ideal.span {B.equivFun.symm ![304, 107, 11]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E109RS0 


noncomputable def E109RS2 : RelationCertificate Table 98 ![![109, 0, 0], ![-1, 1, 0]]
  ![-2896, -1030, -107] ![![98, 0, 0], ![38, 1, 0]] where
    su := ![![10682, 0, 0], ![-98, 98, 0]]
    hsu := by decide
    w := ![![-283808, -100940, -10486], ![-138082, -49098, -5096]]
    hw := by decide
    g := ![![![3587035939075, -1042883501461246, -27446786766943], ![-9250776895581, 2689785103160461, 0]], ![![-65817180158, 19135479112946, 503610819579], ![169739043569, -49353860318744, 0]]]
    h := ![![![-52, 16, -1], ![-2772, 2, 0]], ![![-26, 9, -1], ![-1425, 57, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {98} * I109N2 =  Ideal.span {B.equivFun.symm ![-2896, -1030, -107]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E109RS2 


noncomputable def E113RS1 : RelationCertificate Table 14 ![![113, 0, 0], ![-24, 1, 0]]
  ![6, 4, 1] ![![14, 0, 0], ![-4, 1, 0]] where
    su := ![![1582, 0, 0], ![-336, 14, 0]]
    hsu := by decide
    w := ![![84, 56, 14], ![238, 56, 0]]
    hw := by decide
    g := ![![![-85420, -4528061, 1137355], ![-299025, -15922974, 0]], ![![-129760, -6877121, 1727390], ![-454146, -24183459, 0]]]
    h := ![![![102, -4, 0], ![480, 1, 0]], ![![169, -7, 0], ![795, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {14} * I113N1 =  Ideal.span {B.equivFun.symm ![6, 4, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E113RS1 


noncomputable def E127RS0 : RelationCertificate Table 14 ![![127, 0, 0], ![16, 1, 0]]
  ![-50, -3, 1] ![![14, 0, 0], ![-42, -4, 1]] where
    su := ![![1778, 0, 0], ![224, 14, 0]]
    hsu := by decide
    w := ![![-700, -42, 14], ![266, 126, -14]]
    hw := by decide
    g := ![![![-4408357, -259002, -273015], ![13279649, 2364360, 0]], ![![-626445, -36805, -38797], ![1887110, 335988, 0]]]
    h := ![![![-78, -5, 0], ![616, 1, 0]], ![![13, -15, -1], ![-102, 126, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {14} * I127N0 =  Ideal.span {B.equivFun.symm ![-50, -3, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E127RS0 


noncomputable def E127RS2 : RelationCertificate Table 98 ![![127, 0, 0], ![-7, 1, 0]]
  ![-884, -314, -33] ![![98, 0, 0], ![38, 1, 0]] where
    su := ![![12446, 0, 0], ![-686, 98, 0]]
    hsu := by decide
    w := ![![-86632, -30772, -3234], ![-42238, -14994, -1568]]
    hw := by decide
    g := ![![![1152579851629, -335097426347851, -8819151510436], ![-2972442775295, 864276848022753, 0]], ![![-72603461078, 21108500995470, 555537147707], ![187240504889, -54442640475288, 0]]]
    h := ![![![-614798, 88089, -38], ![-11154066, 4793, 0]], ![![-299737, 42950, -19], ![-5438024, 2397, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {98} * I127N2 =  Ideal.span {B.equivFun.symm ![-884, -314, -33]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS2 


noncomputable def E131RS0 : RelationCertificate Table 2 ![![131, 0, 0], ![0, 1, 0]]
  ![0, 1, 0] ![![2, 0, 0], ![-44, -4, 1]] where
    su := ![![262, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![0, 2, 0], ![262, 22, -4]]
    hw := by decide
    g := ![![![470, 0, -11], ![5, 1, 1]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![1, 0, 0], ![11, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {2} * I131N0 =  Ideal.span {B.equivFun.symm ![0, 1, 0]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E131RS0 


noncomputable def E137RS1 : RelationCertificate Table 2 ![![137, 0, 0], ![-19, 1, 0]]
  ![-42, 14, -1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![274, 0, 0], ![-38, 2, 0]]
    hsu := by decide
    w := ![![-84, 28, -2], ![-262, -108, 14]]
    hw := by decide
    g := ![![![-599, -170, -22], ![-85, 0, 0]], ![![41, 11, 3], ![7, -3, 0]]]
    h := ![![![-1464, 96, -1], ![-10554, 136, 0]], ![![-4607, 262, -1], ![-33212, 144, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {2} * I137N1 =  Ideal.span {B.equivFun.symm ![-42, 14, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E137RS1 
