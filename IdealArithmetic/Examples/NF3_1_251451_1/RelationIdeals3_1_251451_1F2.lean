import IdealArithmetic.Examples.NF3_1_251451_1.PrimesBelow3_1_251451_1F2
import IdealArithmetic.Examples.NF3_1_251451_1.ClassGroupData3_1_251451_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 7 ![![83, 0, 0], ![-38, 1, 0]]
  ![-64940, -2240, -1723] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![581, 0, 0], ![-266, 7, 0]]
    hsu := by decide
    w := ![![-454580, -15680, -12061], ![-84427, -2912, -2240]]
    hw := by decide
    g := ![![![64, -43, -149], ![-2, 1011, 0]], ![![-32, 22, 65], ![4, -444, 0]]]
    h := ![![![-20180220, 606526, -2008], ![-44076140, 164941, 0]], ![![-3747953, 112649, -373], ![-8186001, 30639, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {7} * I83N1 =  Ideal.span {B.equivFun.symm ![-64940, -2240, -1723]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 7 ![![89, 0, 0], ![-21, 1, 0]]
  ![-409, 364, -38] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![623, 0, 0], ![-147, 7, 0]]
    hsu := by decide
    w := ![![-2863, 2548, -266], ![-1862, 959, 364]]
    hw := by decide
    g := ![![![-129945, -4393, 315382], ![-625, -2231808, 0]], ![![28763, 972, -70849], ![141, 501285, 0]]]
    h := ![![![-2228, 122, -1], ![-9423, 51, 0]], ![![-1456, 83, 0], ![-6158, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {7} * I89N1 =  Ideal.span {B.equivFun.symm ![-409, 364, -38]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![42, 1, 0]]
  ![9, -7, 0] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![202, 0, 0], ![84, 2, 0]]
    hsu := by decide
    w := ![![18, -14, 0], ![-118, 86, 2]]
    hw := by decide
    g := ![![![-10, 5, 12], ![-73, 0, 0]], ![![-8, 2, 5], ![-31, 0, 0]]]
    h := ![![![213, 5, 0], ![-512, 0, 0]], ![![-1807, -85, -1], ![4344, 102, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![9, -7, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 14 ![![107, 0, 0], ![42, 1, 0]]
  ![874450, 30163, 23201] ![![14, 0, 0], ![21, 1, 1]] where
    su := ![![1498, 0, 0], ![588, 14, 0]]
    hsu := by decide
    w := ![![12242300, 422282, 324814], ![20978286, 723618, 556598]]
    hw := by decide
    g := ![![![4603339, -4881538, -173130], ![6544004, -4119819, 0]], ![![1827284, -1937719, -68724], ![2597625, -1635348, 0]]]
    h := ![![![251292158, 7586927, 38400], ![-640175868, -4085599, 0]], ![![430611843, 13000891, 65802], ![-1096999256, -7001057, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {14} * I107N1 =  Ideal.span {B.equivFun.symm ![874450, 30163, 23201]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 7 ![![109, 0, 0], ![31, 1, 0]]
  ![68, 14, -51] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![763, 0, 0], ![217, 7, 0]]
    hsu := by decide
    w := ![![476, 98, -357], ![-2499, 1904, 14]]
    hw := by decide
    g := ![![![74842, 2529, -126913], ![368, 902291, 0]], ![![22178, 749, -38310], ![112, 272289, 0]]]
    h := ![![![7390, 253, 0], ![-25982, -51, 0]], ![![-38689, -1432, -6], ![136024, 656, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {7} * I109N0 =  Ideal.span {B.equivFun.symm ![68, 14, -51]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 14 ![![109, 0, 0], ![-18, 1, 0]]
  ![227, -133, -32] ![![14, 0, 0], ![21, 1, 1]] where
    su := ![![1526, 0, 0], ![-252, 14, 0]]
    hsu := by decide
    w := ![![3178, -1862, -448], ![-3318, 1806, 574]]
    hw := by decide
    g := ![![![8201, -912, -187], ![12249, -800, 0]], ![![-1277, 143, 28], ![-1871, 126, 0]]]
    h := ![![![58115, -3307, 4], ![351906, -468, 0]], ![![-60609, 3465, -5], ![-367008, 586, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {14} * I109N1 =  Ideal.span {B.equivFun.symm ![227, -133, -32]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 2 ![![109, 0, 0], ![-13, 1, 0]]
  ![-36, -1, -1] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![218, 0, 0], ![-26, 2, 0]]
    hsu := by decide
    w := ![![-72, -2, -2], ![-998, -38, -26]]
    hw := by decide
    g := ![![![-6, -7, -1], ![1, 0, 0]], ![![-1, 1, 0], ![0, 0, 0]]]
    h := ![![![-184, 27, -1], ![-1540, 108, 0]], ![![-2861, 231, -1], ![-23950, 96, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {2} * I109N2 =  Ideal.span {B.equivFun.symm ![-36, -1, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E109RS2 


noncomputable def E137RS0 : RelationCertificate Table 2 ![![137, 0, 0], ![29, 1, 0]]
  ![-54387, -1876, -1443] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![274, 0, 0], ![58, 2, 0]]
    hsu := by decide
    w := ![![-108774, -3752, -2886], ![-1522306, -52510, -40390]]
    hw := by decide
    g := ![![![0, -96, 49], ![3, 0, 0]], ![![1, -34, 9], ![2, 0, 0]]]
    h := ![![![-507049, -18397, -42], ![2393494, 4311, 0]], ![![-7095685, -257079, -575], ![33494748, 58580, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {2} * I137N0 =  Ideal.span {B.equivFun.symm ![-54387, -1876, -1443]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 14 ![![137, 0, 0], ![43, 1, 0]]
  ![15, -14, 1] ![![14, 0, 0], ![21, 1, 1]] where
    su := ![![1918, 0, 0], ![602, 14, 0]]
    hsu := by decide
    w := ![![210, -196, 14], ![-322, 238, -14]]
    hw := by decide
    g := ![![![-2332, 2442, 87], ![-3310, 2061, 0]], ![![-756, 789, 28], ![-1068, 666, 0]]]
    h := ![![![104, 2, 0], ![-331, 1, 0]], ![![-320, -50, -1], ![1019, 136, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {14} * I137N1 =  Ideal.span {B.equivFun.symm ![15, -14, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 7 ![![137, 0, 0], ![65, 1, 0]]
  ![22, 0, 1] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![959, 0, 0], ![455, 7, 0]]
    hsu := by decide
    w := ![![154, 0, 7], ![49, -14, 0]]
    hw := by decide
    g := ![![![4, 0, 209000], ![7, -1462998, 0]], ![![2, 0, 104500], ![3, -731499, 0]]]
    h := ![![![5166, 79, 0], ![-10888, 1, 0]], ![![1561, 24, 0], ![-3290, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {7} * I137N2 =  Ideal.span {B.equivFun.symm ![22, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E137RS2 
