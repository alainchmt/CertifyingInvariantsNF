import IdealArithmetic.Examples.NF3_1_466627_1.PrimesBelow3_1_466627_1F2
import IdealArithmetic.Examples.NF3_1_466627_1.ClassGroupData3_1_466627_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 288 ![![83, 0, 0], ![15, 1, 0]]
  ![-403, -57, 5] ![![288, 0, 0], ![68, 1, 0]] where
    su := ![![23904, 0, 0], ![4320, 288, 0]]
    hsu := by decide
    w := ![![-116064, -16416, 1440], ![-25344, -3744, 288]]
    hw := by decide
    g := ![![![-341, 358629, 5274], ![1453, -1518920, 0]], ![![-85, 65823, 968], ![361, -278785, 0]]]
    h := ![![![-1212926, -84538, -245], ![6711497, 20340, 0]], ![![-264866, -18468, -54], ![1465586, 4483, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {288} * I83N1 =  Ideal.span {B.equivFun.symm ![-403, -57, 5]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E83RS1 


noncomputable def E89RS0 : RelationCertificate Table 9 ![![89, 0, 0], ![-38, 1, 0]]
  ![-59, -6, 1] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![801, 0, 0], ![-342, 9, 0]]
    hsu := by decide
    w := ![![-531, -54, 9], ![648, 72, -9]]
    hw := by decide
    g := ![![![21, 72, -18], ![7, 160, 0]], ![![-6, -21, 5], ![6, -44, 0]]]
    h := ![![![-21115, 670, -3], ![-49452, 268, 0]], ![![25828, -756, 2], ![60490, -179, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {9} * I89N0 =  Ideal.span {B.equivFun.symm ![-59, -6, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 9 ![![89, 0, 0], ![-26, 1, 0]]
  ![71, 24, 2] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![801, 0, 0], ![-234, 9, 0]]
    hsu := by decide
    w := ![![639, 216, 18], ![540, 189, 18]]
    hw := by decide
    g := ![![![-6193, -148996, 37632], ![-13792, -338682, 0]], ![![-1535562, -37237840, 9405434], ![-3455063, -84648908, 0]]]
    h := ![![![699, -26, 0], ![2390, 2, 0]], ![![620, -23, 0], ![2120, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {9} * I89N1 =  Ideal.span {B.equivFun.symm ![71, 24, 2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 288 ![![97, 0, 0], ![-10, 1, 0]]
  ![6839, 645, -97] ![![288, 0, 0], ![68, 1, 0]] where
    su := ![![27936, 0, 0], ![-2880, 288, 0]]
    hsu := by decide
    w := ![![1969632, 185760, -27936], ![425088, 40320, -6048]]
    hw := by decide
    g := ![![![102448339565343, -131929355868591823, -1940159742085599], ![-433898849923824, 558766005720652477, 0]], ![![-10913740639446, 14054330004576514, 206683683834741], ![46222901531771, -59524900944405409, 0]]]
    h := ![![![20872057, -2107872, 2067], ![202458269, -200596, 0]], ![![4504628, -454922, 446], ![43694744, -43283, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {288} * I97N1 =  Ideal.span {B.equivFun.symm ![6839, 645, -97]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 24 ![![101, 0, 0], ![-21, 1, 0]]
  ![-1, -3, -1] ![![24, 0, 0], ![-4, 1, 0]] where
    su := ![![2424, 0, 0], ![-504, 24, 0]]
    hsu := by decide
    w := ![![-24, -72, -24], ![-408, -96, 0]]
    hw := by decide
    g := ![![![-12, 239, -60], ![19, 1444, 0]], ![![4, -48, 12], ![1, -289, 0]]]
    h := ![![![-509, 45, -1], ![-2448, 100, 0]], ![![-9241, 461, -1], ![-44444, 101, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {24} * I101N1 =  Ideal.span {B.equivFun.symm ![-1, -3, -1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 16 ![![103, 0, 0], ![0, 1, 0]]
  ![-103, -5, 1] ![![16, 0, 0], ![4, 1, 0]] where
    su := ![![1648, 0, 0], ![0, 16, 0]]
    hsu := by decide
    w := ![![-1648, -80, 16], ![0, -16, 0]]
    hw := by decide
    g := ![![![-1, -4, -1], ![5, 15, 0]], ![![0, 0, 0], ![-1, 0, 0]]]
    h := ![![![-1, 0, 0], ![-5, 1, 0]], ![![0, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {16} * I103N0 =  Ideal.span {B.equivFun.symm ![-103, -5, 1]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 96 ![![103, 0, 0], ![14, 1, 0]]
  ![-1159, -117, 17] ![![96, 0, 0], ![-28, 1, 0]] where
    su := ![![9888, 0, 0], ![1344, 96, 0]]
    hsu := by decide
    w := ![![-111264, -11232, 1632], ![39456, 3936, -576]]
    hw := by decide
    g := ![![![3762299387231, 1343678352574704, -47993311443213], ![12899312184792, 4607357898548443, 0]], ![![499204776073, 178287420026021, -6368044598858], ![1711559232251, 611332281490367, 0]]]
    h := ![![![-1228449, -89765, -144], ![9037792, 14849, 0]], ![![435597, 31815, 50], ![-3204720, -5156, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {96} * I103N1 =  Ideal.span {B.equivFun.symm ![-1159, -117, 17]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 72 ![![103, 0, 0], ![-15, 1, 0]]
  ![-167, 3, 1] ![![72, 0, 0], ![-4, 1, 0]] where
    su := ![![7416, 0, 0], ![-1080, 72, 0]]
    hsu := by decide
    w := ![![-12024, 216, 72], ![1080, -72, 0]]
    hw := by decide
    g := ![![![40101753, 52132274018, -13035574864], ![721831554, 938561390209, 0]], ![![-6230084, -8099109915, 2025166859], ![-112141513, -145812013848, 0]]]
    h := ![![![-203009, 13789, -17], ![-1393984, 1752, 0]], ![![18255, -1232, 1], ![125350, -103, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {72} * I103N2 =  Ideal.span {B.equivFun.symm ![-167, 3, 1]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E103RS2 


noncomputable def E107RS0 : RelationCertificate Table 12 ![![107, 0, 0], ![35, 1, 0]]
  ![-49, -15, -1] ![![12, 0, 0], ![-4, 1, 0]] where
    su := ![![1284, 0, 0], ![420, 12, 0]]
    hsu := by decide
    w := ![![-588, -180, -12], ![-216, -96, -12]]
    hw := by decide
    g := ![![![76117, 3042772, -765447], ![228202, 9185357, 0]], ![![24187, 966865, -243227], ![72519, 2918722, 0]]]
    h := ![![![-637, -53, -1], ![1946, 106, 0]], ![![-254, -42, -1], ![776, 106, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {12} * I107N0 =  Ideal.span {B.equivFun.symm ![-49, -15, -1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 12 ![![107, 0, 0], ![36, 1, 0]]
  ![-11, 3, 1] ![![12, 0, 0], ![-4, 1, 0]] where
    su := ![![1284, 0, 0], ![432, 12, 0]]
    hsu := by decide
    w := ![![-132, 36, 12], ![456, 84, 0]]
    hw := by decide
    g := ![![![33, -276, 70], ![-31, -847, 0]], ![![10, -95, 24], ![-7, -290, 0]]]
    h := ![![![11, -36, -1], ![-33, 108, 0]], ![![34, 1, 0], ![-100, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {12} * I107N1 =  Ideal.span {B.equivFun.symm ![-11, 3, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 4 ![![109, 0, 0], ![16, 1, 0]]
  ![-29, -11, -1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![436, 0, 0], ![64, 4, 0]]
    hsu := by decide
    w := ![![-116, -44, -4], ![-412, -136, -12]]
    hw := by decide
    g := ![![![14, -4, -65], ![-1, 261, 0]], ![![3, -1, -10], ![3, 40, 0]]]
    h := ![![![-1393, -103, -1], ![9488, 108, 0]], ![![-4899, -322, -1], ![33368, 106, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {4} * I109N1 =  Ideal.span {B.equivFun.symm ![-29, -11, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E109RS1 


noncomputable def E127RS1 : RelationCertificate Table 48 ![![127, 0, 0], ![35, 1, 0]]
  ![1063, 357, 31] ![![48, 0, 0], ![20, 1, 0]] where
    su := ![![6096, 0, 0], ![1680, 48, 0]]
    hsu := by decide
    w := ![![51024, 17136, 1488], ![34032, 11520, 1008]]
    hw := by decide
    g := ![![![-1760536, 238014405, 11905123], ![4225099, -571445847, 0]], ![![-17190669031, 2324178448782, 116251899112], ![41257605632, -5580091157363, 0]]]
    h := ![![![1077194, 34341, 102], ![-3908645, -12923, 0]], ![![718482, 22904, 68], ![-2607043, -8615, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {48} * I127N1 =  Ideal.span {B.equivFun.symm ![1063, 357, 31]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 36 ![![127, 0, 0], ![-39, 1, 0]]
  ![-13, -3, -1] ![![36, 0, 0], ![-4, 1, 0]] where
    su := ![![4572, 0, 0], ![-1404, 36, 0]]
    hsu := by decide
    w := ![![-468, -108, -36], ![-360, -108, 0]]
    hw := by decide
    g := ![![![-1673, -546192, 136652], ![-14977, -4919469, 0]], ![![519, 169163, -42323], ![4644, 1523627, 0]]]
    h := ![![![-19162, 569, -2], ![-62399, 253, 0]], ![![-14782, 418, -1], ![-48136, 127, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {36} * I127N2 =  Ideal.span {B.equivFun.symm ![-13, -3, -1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E127RS2 


noncomputable def E131RS1 : RelationCertificate Table 12 ![![131, 0, 0], ![38, 1, 0]]
  ![-83, -9, 1] ![![12, 0, 0], ![-4, 1, 0]] where
    su := ![![1572, 0, 0], ![456, 12, 0]]
    hsu := by decide
    w := ![![-996, -108, 12], ![744, 60, -12]]
    hw := by decide
    g := ![![![238717, 9547883, -2401889], ![716085, 28822664, 0]], ![![69522, 2780633, -699503], ![208550, 8394035, 0]]]
    h := ![![![-22027, -656, -2], ![75933, 263, 0]], ![![16366, 469, 1], ![-56418, -132, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {12} * I131N1 =  Ideal.span {B.equivFun.symm ![-83, -9, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 32 ![![137, 0, 0], ![-22, 1, 0]]
  ![1333, 127, -19] ![![32, 0, 0], ![4, 1, 0]] where
    su := ![![4384, 0, 0], ![-704, 32, 0]]
    hsu := by decide
    w := ![![42656, 4064, -608], ![-2496, -192, 32]]
    hw := by decide
    g := ![![![-32778355, 8522374783, 2132642343], ![262226932, -68244554963, 0]], ![![5343356, -1389272761, -347652150], ![-42746853, 11124868799, 0]]]
    h := ![![![1044853, -48529, 47], ![6506524, -6458, 0]], ![![-61114, 2844, -3], ![-380570, 412, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {32} * I137N1 =  Ideal.span {B.equivFun.symm ![1333, 127, -19]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E137RS1 
