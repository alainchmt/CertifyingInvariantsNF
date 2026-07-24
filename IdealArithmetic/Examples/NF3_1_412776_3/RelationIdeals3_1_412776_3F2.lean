import IdealArithmetic.Examples.NF3_1_412776_3.PrimesBelow3_1_412776_3F2
import IdealArithmetic.Examples.NF3_1_412776_3.ClassGroupData3_1_412776_3

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 242 ![![83, 0, 0], ![-24, 1, 0]]
  ![1378, 91, 47] ![![242, 0, 0], ![-83, 2, 1]] where
    su := ![![20086, 0, 0], ![-5808, 242, 0]]
    hsu := by decide
    w := ![![333476, 22022, 11374], ![-93654, -6050, -3146]]
    hw := by decide
    g := ![![![-82909, 86056, -3440], ![29233, 200808, 0]], ![![22529, -23313, 931], ![-7714, -54396, 0]]]
    h := ![![![9936518, -439681, 2139], ![34363734, -88745, 0]], ![![-2790561, 123483, -601], ![-9650674, 24935, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {242} * I83N1 =  Ideal.span {B.equivFun.symm ![1378, 91, 47]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 22 ![![89, 0, 0], ![1, 1, 0]]
  ![-34, 10, -1] ![![22, 0, 0], ![5, 2, 1]] where
    su := ![![1958, 0, 0], ![22, 22, 0]]
    hsu := by decide
    w := ![![-748, 220, -22], ![726, -242, 22]]
    hw := by decide
    g := ![![![104127, -17619, 2890], ![22199, -21449, 0]], ![![-6, -2, -1], ![21, 0, 0]]]
    h := ![![![0, 0, -1], ![-34, 44, 0]], ![![0, 0, 1], ![33, -44, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {22} * I89N1 =  Ideal.span {B.equivFun.symm ![-34, 10, -1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 242 ![![97, 0, 0], ![47, 1, 0]]
  ![-2318, 630, -19] ![![242, 0, 0], ![-83, 2, 1]] where
    su := ![![23474, 0, 0], ![11374, 242, 0]]
    hsu := by decide
    w := ![![-560956, 152460, -4598], ![258698, -70422, 2178]]
    hw := by decide
    g := ![![![176529, -182421, 7320], ![-62021, -425790, 0]], ![![85742, -88492, 3551], ![-29857, -206550, 0]]]
    h := ![![![-12638164, -375364, -4531], ![26082970, 219744, 0]], ![![5828278, 173092, 2089], ![-12028551, -101312, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {242} * I97N1 =  Ideal.span {B.equivFun.symm ![-2318, 630, -19]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 11 ![![101, 0, 0], ![-49, 1, 0]]
  ![45, -164, 78] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![1111, 0, 0], ![-539, 11, 0]]
    hsu := by decide
    w := ![![495, -1804, 858], ![8646, -1265, -484]]
    hw := by decide
    g := ![![![40863, 3835, 1156], ![-7071, 1735, 0]], ![![-18241, -1723, -506], ![3166, -830, 0]]]
    h := ![![![1142, -6, 0], ![2353, 39, 0]], ![![19274, -405, 0], ![39712, -22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {11} * I101N1 =  Ideal.span {B.equivFun.symm ![45, -164, 78]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 121 ![![103, 0, 0], ![20, 1, 0]]
  ![1629, 111, 56] ![![121, 0, 0], ![9, 1, 0]] where
    su := ![![12463, 0, 0], ![2420, 121, 0]]
    hsu := by decide
    w := ![![197109, 13431, 6776], ![20933, 1452, 726]]
    hw := by decide
    g := ![![![-118896, 194483206, 43221426], ![1598515, -2614896276, 0]], ![![-31338, 51256531, 11391114], ![421326, -689162398, 0]]]
    h := ![![![2974943, 155882, 714], ![-15320875, -36743, 0]], ![![315911, 16535, 74], ![-1626933, -3808, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {121} * I103N1 =  Ideal.span {B.equivFun.symm ![1629, 111, 56]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E103RS1 


noncomputable def E109RS0 : RelationCertificate Table 242 ![![109, 0, 0], ![-50, 1, 0]]
  ![-18806, -1283, -656] ![![242, 0, 0], ![29, 1, 1]] where
    su := ![![26378, 0, 0], ![-12100, 242, 0]]
    hsu := by decide
    w := ![![-4551052, -310486, -158752], ![-762542, -52030, -26620]]
    hw := by decide
    g := ![![![-54061050046569, -3890275455781, -952429164460], ![-6498401470793, 118493096715952, 8229780]], ![![24258163482070, 1745636422440, 427372060969], ![2915949377986, -53169979294848, -3692850]]]
    h := ![![![-329334, 7321, -36], ![-717572, 1634, 0]], ![![-55139, 1225, -6], ![-120140, 272, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {242} * I109N0 =  Ideal.span {B.equivFun.symm ![-18806, -1283, -656]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 242 ![![109, 0, 0], ![-38, 1, 0]]
  ![-7522, -515, -262] ![![242, 0, 0], ![29, 1, 1]] where
    su := ![![26378, 0, 0], ![-9196, 242, 0]]
    hsu := by decide
    w := ![![-1820324, -124630, -63404], ![-305162, -20812, -10648]]
    hw := by decide
    g := ![![![-413571047800682242, -29760889130880304, -7286152281169628], ![-49713253833189229, 906481052936431440, 422040]], ![![103392762829709673, 7440222346012384, 1821538085787824], ![12428313564022276, -226620265161915800, -105510]]]
    h := ![![![-85968434, 2459229, -10366], ![-246593468, 564816, 0]], ![![-14411871, 412273, -1738], ![-41339281, 94699, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {242} * I109N1 =  Ideal.span {B.equivFun.symm ![-7522, -515, -262]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 242 ![![109, 0, 0], ![-21, 1, 0]]
  ![-292630, -19973, -10216] ![![242, 0, 0], ![29, 1, 1]] where
    su := ![![26378, 0, 0], ![-5082, 242, 0]]
    hsu := by decide
    w := ![![-70816460, -4833466, -2472272], ![-11867438, -809974, -414304]]
    hw := by decide
    g := ![![![-1705571052693917, -122734199353359, -30048163614136], ![-205017945830785, 3738336733508300, 9179370]], ![![313668239574297, 22571806777515, 5526099055445], ![37704449807889, -687510203860130, -1688160]]]
    h := ![![![-1882612, 91860, -334], ![-9757718, 13095, 0]], ![![-315463, 15393, -56], ![-1635068, 2196, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {242} * I109N2 =  Ideal.span {B.equivFun.symm ![-292630, -19973, -10216]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E109RS2 


noncomputable def E131RS0 : RelationCertificate Table 121 ![![131, 0, 0], ![18, 1, 0]]
  ![135, -63, 14] ![![121, 0, 0], ![9, 1, 0]] where
    su := ![![15851, 0, 0], ![2178, 121, 0]]
    hsu := by decide
    w := ![![16335, -7623, 1694], ![2783, -726, 0]]
    hw := by decide
    g := ![![![-266085, 435219187, 96721944], ![3577098, -5851677654, 0]], ![![-39075, 63906324, 14202370], ![525297, -859243392, 0]]]
    h := ![![![819, 44, 0], ![-5953, 7, 0]], ![![127, 7, 0], ![-923, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {121} * I131N0 =  Ideal.span {B.equivFun.symm ![135, -63, 14]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E131RS0 


noncomputable def E131RS1 : RelationCertificate Table 121 ![![131, 0, 0], ![25, 1, 0]]
  ![77859, 5314, 2718] ![![121, 0, 0], ![9, 1, 0]] where
    su := ![![15851, 0, 0], ![3025, 121, 0]]
    hsu := by decide
    w := ![![9420939, 642994, 328878], ![1005147, 68607, 35090]]
    hw := by decide
    g := ![![![-21, 46795, 10400], ![470, -629223, 0]], ![![-8, 9224, 2050], ![139, -124032, 0]]]
    h := ![![![294214, 12201, 54], ![-1538567, -2178, 0]], ![![31372, 1279, 4], ![-164057, -117, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {121} * I131N1 =  Ideal.span {B.equivFun.symm ![77859, 5314, 2718]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E131RS1 


noncomputable def E131RS2 : RelationCertificate Table 121 ![![131, 0, 0], ![-43, 1, 0]]
  ![351, -67, -12] ![![121, 0, 0], ![9, 1, 0]] where
    su := ![![15851, 0, 0], ![-5203, 121, 0]]
    hsu := by decide
    w := ![![42471, -8107, -1452], ![1815, 0, -242]]
    hw := by decide
    g := ![![![645009, -1055153846, -234494560], ![-8672212, 14186920813, 0]], ![![-201520, 329655338, 73261718], ![2709451, -4432333919, 0]]]
    h := ![![![9657, -227, 0], ![29412, -6, 0]], ![![459, -11, 0], ![1398, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {121} * I131N2 =  Ideal.span {B.equivFun.symm ![351, -67, -12]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E131RS2 


noncomputable def E137RS1 : RelationCertificate Table 11 ![![137, 0, 0], ![10, 1, 0]]
  ![57, 2, 2] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![1507, 0, 0], ![110, 11, 0]]
    hsu := by decide
    w := ![![627, 22, 22], ![110, 11, 0]]
    hw := by decide
    g := ![![![-3, -220, 222], ![-14, -1222, 0]], ![![0, -20, 20], ![1, -110, 0]]]
    h := ![![![5461, 546, 0], ![-74810, 1, 0]], ![![950, 95, 0], ![-13014, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {11} * I137N1 =  Ideal.span {B.equivFun.symm ![57, 2, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E137RS1 
