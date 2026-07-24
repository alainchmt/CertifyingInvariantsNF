import IdealArithmetic.Examples.NF3_1_672300_4.PrimesBelow3_1_672300_4F2
import IdealArithmetic.Examples.NF3_1_672300_4.ClassGroupData3_1_672300_4

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 7 ![![83, 0, 0], ![13, 1, 0]]
  ![13, 1, 0] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![581, 0, 0], ![91, 7, 0]]
    hsu := by decide
    w := ![![91, 7, 0], ![28, 14, 7]]
    hw := by decide
    g := ![![![11097841, -1120005, 229963], ![3010813, 0, -536580]], ![![1765565, -178183, 36585], ![478996, 0, -85365]]]
    h := ![![![-80, -480, -280], ![1, 3320, 0]], ![![-28, -146, -85], ![24, 1008, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {7} * I83N0 =  Ideal.span {B.equivFun.symm ![13, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 7 ![![83, 0, 0], ![35, 1, 0]]
  ![11629, 649, 616] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![581, 0, 0], ![245, 7, 0]]
    hsu := by decide
    w := ![![81403, 4543, 4312], ![120652, 6734, 6391]]
    hw := by decide
    g := ![![![6321, -632, 122], ![1719, 0, -303]], ![![2717, -272, 53], ![745, 0, -131]]]
    h := ![![![-86375, -1894407, -390166], ![-59198, 4626342, 0]], ![![-128011, -2807807, -578287], ![-87765, 6856962, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {7} * I83N1 =  Ideal.span {B.equivFun.symm ![11629, 649, 616]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E83RS1 


noncomputable def E97RS1 : RelationCertificate Table 7 ![![97, 0, 0], ![-12, 1, 0]]
  ![-19, -16, 14] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![679, 0, 0], ![-84, 7, 0]]
    hsu := by decide
    w := ![![-133, -112, 98], ![2114, -161, -70]]
    hw := by decide
    g := ![![![-30259, 3197, -583], ![-8182, 0, 1521]], ![![3552, -365, 72], ![970, 0, -174]]]
    h := ![![![1841, -12191, 6566], ![-281, -90984, 0]], ![![-32848, 218614, -117751], ![6402, 1631691, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {7} * I97N1 =  Ideal.span {B.equivFun.symm ![-19, -16, 14]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 49 ![![101, 0, 0], ![5, 1, 0]]
  ![2491, 139, 132] ![![49, 0, 0], ![3, -10, 1]] where
    su := ![![4949, 0, 0], ![245, 49, 0]]
    hsu := by decide
    w := ![![122059, 6811, 6468], ![-173999, -9702, -9212]]
    hw := by decide
    g := ![![![-45, 6, -1], ![-4, 0, 0]], ![![-5, 4, 0], ![20, 0, 0]]]
    h := ![![![19537151, 39195023, 68614772], ![1355296, -990013120, 0]], ![![-27850851, -55873786, -97812598], ![-1931932, 1411296030, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {49} * I101N1 =  Ideal.span {B.equivFun.symm ![2491, 139, 132]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 7 ![![103, 0, 0], ![-51, 1, 0]]
  ![339, 19, 18] ![![7, 0, 0], ![3, -3, 1]] where
    su := ![![721, 0, 0], ![-357, 7, 0]]
    hsu := by decide
    w := ![![2373, 133, 126], ![-3801, -210, -203]]
    hw := by decide
    g := ![![![-37, -4, 5], ![-10, 0, 0]], ![![22, 3, -3], ![9, 0, 0]]]
    h := ![![![-364, 15300, -2060], ![447, 30314, 0]], ![![678, -24519, 3301], ![-525, -48576, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {7} * I103N1 =  Ideal.span {B.equivFun.symm ![339, 19, 18]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 49 ![![107, 0, 0], ![-32, 1, 0]]
  ![-11, -3, 0] ![![49, 0, 0], ![-18, 4, 1]] where
    su := ![![5243, 0, 0], ![-1568, 49, 0]]
    hsu := by decide
    w := ![![-539, -147, 0], ![-294, 49, -98]]
    hw := by decide
    g := ![![![-4333, -20, 137], ![1604, 0, 362]], ![![1228, 4, -39], ![-432, 0, -102]]]
    h := ![![![9201, -172913, 36687], ![-4283, -560787, 0]], ![![5260, -98577, 20915], ![-2393, -319701, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {49} * I107N1 =  Ideal.span {B.equivFun.symm ![-11, -3, 0]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 49 ![![109, 0, 0], ![0, 1, 0]]
  ![30657, 1711, 1624] ![![49, 0, 0], ![-18, 4, 1]] where
    su := ![![5341, 0, 0], ![0, 49, 0]]
    hsu := by decide
    w := ![![1502193, 83839, 79576], ![810362, 45227, 42924]]
    hw := by decide
    g := ![![![318734885, 1417272, -10102525], ![-117176746, 0, -26617408]], ![![1342996, 5968, -42567], ![-493684, 0, -112152]]]
    h := ![![![-2973729, 1486895, -10409021], ![13715, 162083559, 0]], ![![-1604186, 802109, -5615174], ![7448, 87436406, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {49} * I109N0 =  Ideal.span {B.equivFun.symm ![30657, 1711, 1624]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 49 ![![109, 0, 0], ![7, 1, 0]]
  ![125, 8, 7] ![![49, 0, 0], ![-18, 4, 1]] where
    su := ![![5341, 0, 0], ![343, 49, 0]]
    hsu := by decide
    w := ![![6125, 392, 343], ![3724, 147, 196]]
    hw := by decide
    g := ![![![101171493, 449859, -3206700], ![-37193714, 0, -8448784]], ![![8057909, 35829, -255401], ![-2962326, 0, -672912]]]
    h := ![![![947694, 2859059, 3336501], ![87093, -51954086, 0]], ![![576373, 1738854, 2029231], ![53067, -31598025, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {49} * I109N1 =  Ideal.span {B.equivFun.symm ![125, 8, 7]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 49 ![![109, 0, 0], ![-7, 1, 0]]
  ![185, -150, 98] ![![49, 0, 0], ![-18, 4, 1]] where
    su := ![![5341, 0, 0], ![-343, 49, 0]]
    hsu := by decide
    w := ![![9065, -7350, 4802], ![37338, 3920, -6419]]
    hw := by decide
    g := ![![![103850681, 460934, -3292564], ![-38178782, 0, -8673320]], ![![-5372189, -23901, 170263], ![1975019, 0, 448620]]]
    h := ![![![-571502, 2300341, -2013263], ![57841, 31349395, 0]], ![![-2286209, 9202153, -8053741], ![231275, 125408234, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {49} * I109N2 =  Ideal.span {B.equivFun.symm ![185, -150, 98]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E109RS2 


noncomputable def E131RS0 : RelationCertificate Table 49 ![![131, 0, 0], ![39, 1, 0]]
  ![-991957, -55363, -52546] ![![49, 0, 0], ![-7, 0, 1]] where
    su := ![![6419, 0, 0], ![1911, 49, 0]]
    hsu := by decide
    w := ![![-48605893, -2712787, -2574754], ![-3899861, -217658, -206584]]
    hw := by decide
    g := ![![![-70761, 7412, -671], ![10098, 22632, 0]], ![![-21641, 2266, -205], ![3134, 6923, 0]]]
    h := ![![![7171243296, 154997440464, 28556825684], ![3318136953, -534420602450, 0]], ![![575379834, 12436114985, 2291237628], ![266228579, -42878876212, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {49} * I131N0 =  Ideal.span {B.equivFun.symm ![-991957, -55363, -52546]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E131RS0 


noncomputable def E131RS1 : RelationCertificate Table 49 ![![131, 0, 0], ![-35, 1, 0]]
  ![-1067, -60, -56] ![![49, 0, 0], ![-19, 1, 0]] where
    su := ![![6419, 0, 0], ![-1715, 49, 0]]
    hsu := by decide
    w := ![![-52283, -2940, -2744], ![11417, 637, 588]]
    hw := by decide
    g := ![![![703349, -8756442, 3067732], ![-451374, -21475596, -572]], ![![-179519, 2235037, -783023], ![115230, 5481537, 146]]]
    h := ![![![-10863275, 217445202, -42287784], ![4562382, 791385664, 0]], ![![2372238, -47483528, 9234387], ![-996199, -172814955, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {49} * I131N1 =  Ideal.span {B.equivFun.symm ![-1067, -60, -56]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E131RS1 


noncomputable def E131RS2 : RelationCertificate Table 7 ![![131, 0, 0], ![-4, 1, 0]]
  ![-51, 10, -3] ![![7, 0, 0], ![3, -3, 1]] where
    su := ![![917, 0, 0], ![-28, 7, 0]]
    hsu := by decide
    w := ![![-357, 70, -21], ![2625, -21, -224]]
    hw := by decide
    g := ![![![-1340, -278, -17], ![-449, 0, 0]], ![![-46, -8, -1], ![-12, 0, 0]]]
    h := ![![![-4425, 11084, -15521], ![326, 290464, 0]], ![![32501, -81350, 113906], ![-1523, -2131674, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {7} * I131N2 =  Ideal.span {B.equivFun.symm ![-51, 10, -3]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E131RS2 


noncomputable def E137RS1 : RelationCertificate Table 7 ![![137, 0, 0], ![-59, 1, 0]]
  ![23, 0, 1] ![![7, 0, 0], ![7, 0, 1]] where
    su := ![![959, 0, 0], ![-413, 7, 0]]
    hsu := by decide
    w := ![![161, 0, 7], ![203, 21, 21]]
    hw := by decide
    g := ![![![14069, -357, -1795], ![13814, -1251, 0]], ![![-5871, 149, 749], ![-5764, 522, 0]]]
    h := ![![![554, -20295, 2368], ![-285, -46345, 0]], ![![662, -25548, 2981], ![-441, -58342, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {7} * I137N1 =  Ideal.span {B.equivFun.symm ![23, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E137RS1 
