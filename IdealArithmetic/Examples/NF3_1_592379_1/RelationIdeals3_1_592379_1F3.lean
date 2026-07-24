import IdealArithmetic.Examples.NF3_1_592379_1.PrimesBelow3_1_592379_1F3
import IdealArithmetic.Examples.NF3_1_592379_1.ClassGroupData3_1_592379_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 4 ![![139, 0, 0], ![41, 1, 0]]
  ![3, -3, 1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![556, 0, 0], ![164, 4, 0]]
    hsu := by decide
    w := ![![12, -12, 4], ![92, -52, 0]]
    hw := by decide
    g := ![![![143865, -1437370, -754609], ![-287408, 3018449, 0]], ![![41318, -412795, -216714], ![-82537, 866860, 0]]]
    h := ![![![300, 7, 0], ![-1017, 1, 0]], ![![2300, 56, 0], ![-7797, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {4} * I139N1 =  Ideal.span {B.equivFun.symm ![3, -3, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E139RS1 


noncomputable def E149RS0 : RelationCertificate Table 2 ![![149, 0, 0], ![40, 1, 0]]
  ![-1, -1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![298, 0, 0], ![80, 2, 0]]
    hsu := by decide
    w := ![![-2, -2, 2], ![86, -50, 0]]
    hw := by decide
    g := ![![![625, 7, -211], ![4, 447, 0]], ![![175, 2, -55], ![1, 117, 0]]]
    h := ![![![-69, -2, 0], ![257, 1, 0]], ![![407, 10, 0], ![-1515, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N0 : Ideal.span {2} * I149N0 =  Ideal.span {B.equivFun.symm ![-1, -1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E149RS0 


noncomputable def E149RS1 : RelationCertificate Table 112 ![![149, 0, 0], ![-29, 1, 0]]
  ![47357, 671, 943] ![![112, 0, 0], ![30, 1, 0]] where
    su := ![![16688, 0, 0], ![-3248, 112, 0]]
    hsu := by decide
    w := ![![5303984, 75152, 105616], ![1501808, 21280, 29904]]
    hw := by decide
    g := ![![![-62, 13835, 461], ![211, -51645, 0]], ![![1, -2402, -80], ![0, 8965, 0]]]
    h := ![![![426503, -15088, 20], ![2189710, -2037, 0]], ![![120795, -4254, 5], ![620174, -478, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {112} * I149N1 =  Ideal.span {B.equivFun.symm ![47357, 671, 943]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E149RS1 


noncomputable def E149RS2 : RelationCertificate Table 14 ![![149, 0, 0], ![-12, 1, 0]]
  ![41, -3, 1] ![![14, 0, 0], ![2, 1, 0]] where
    su := ![![2086, 0, 0], ![-168, 14, 0]]
    hsu := by decide
    w := ![![574, -42, 14], ![168, -14, 0]]
    hw := by decide
    g := ![![![-69271, 6927240, 3480938], ![484913, -48733131, 0]], ![![5228, -522968, -262791], ![-36597, 3679074, 0]]]
    h := ![![![7141, -595, 0], ![88664, 1, 0]], ![![2100, -175, 0], ![26074, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N2 : Ideal.span {14} * I149N2 =  Ideal.span {B.equivFun.symm ![41, -3, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E149RS2 


noncomputable def E157RS1 : RelationCertificate Table 28 ![![157, 0, 0], ![60, 1, 0]]
  ![1153, 15, 23] ![![28, 0, 0], ![2, 1, 0]] where
    su := ![![4396, 0, 0], ![1680, 28, 0]]
    hsu := by decide
    w := ![![32284, 420, 644], ![4284, 56, 84]]
    hw := by decide
    g := ![![![-6, 943, 471], ![35, -13189, 0]], ![![-3, 374, 187], ![23, -5236, 0]]]
    h := ![![![917869, 19369, 68], ![-2401738, -10653, 0]], ![![121749, 2568, 9], ![-318574, -1410, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {28} * I157N1 =  Ideal.span {B.equivFun.symm ![1153, 15, 23]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E157RS1 


noncomputable def E163RS0 : RelationCertificate Table 56 ![![163, 0, 0], ![56, 1, 0]]
  ![31, -19, -3] ![![56, 0, 0], ![-26, 1, 0]] where
    su := ![![9128, 0, 0], ![3136, 56, 0]]
    hsu := by decide
    w := ![![1736, -1064, -168], ![-1064, 672, 56]]
    hw := by decide
    g := ![![![-10740330, -1574698951, 60581232], ![-23132987, -3392549009, 0]], ![![-3764047, -551868278, 21231271], ![-8107167, -1188951182, 0]]]
    h := ![![![48725, 1039, 3], ![-141824, -492, 0]], ![![-30001, -648, -2], ![87324, 327, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N0 : Ideal.span {56} * I163N0 =  Ideal.span {B.equivFun.symm ![31, -19, -3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E163RS0 


noncomputable def E163RS1 : RelationCertificate Table 28 ![![163, 0, 0], ![-47, 1, 0]]
  ![741, 11, 15] ![![28, 0, 0], ![2, 1, 0]] where
    su := ![![4564, 0, 0], ![-1316, 28, 0]]
    hsu := by decide
    w := ![![20748, 308, 420], ![2772, 28, 56]]
    hw := by decide
    g := ![![![-611, 240260, 120283], ![8550, -3367917, 0]], ![![176, -69770, -34929], ![-2461, 978010, 0]]]
    h := ![![![1127835, -25543, 33], ![3911412, -5364, 0]], ![![150757, -3395, 4], ![522836, -650, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {28} * I163N1 =  Ideal.span {B.equivFun.symm ![741, 11, 15]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E163RS1 


noncomputable def E163RS2 : RelationCertificate Table 2 ![![163, 0, 0], ![-10, 1, 0]]
  ![53, 1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![326, 0, 0], ![-20, 2, 0]]
    hsu := by decide
    w := ![![106, 2, 2], ![86, 4, 2]]
    hw := by decide
    g := ![![![12, -4, 67378], ![-1, -134757, 0]], ![![-1, 0, -3906], ![1, 7812, 0]]]
    h := ![![![181, -18, 0], ![2945, 1, 0]], ![![151, -15, 0], ![2457, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N2 : Ideal.span {2} * I163N2 =  Ideal.span {B.equivFun.symm ![53, 1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E163RS2 


noncomputable def E167RS1 : RelationCertificate Table 112 ![![167, 0, 0], ![-48, 1, 0]]
  ![25, 19, 3] ![![112, 0, 0], ![30, 1, 0]] where
    su := ![![18704, 0, 0], ![-5376, 112, 0]]
    hsu := by decide
    w := ![![2800, 2128, 336], ![1008, 448, 112]]
    hw := by decide
    g := ![![![-270, 118609, 3954], ![1017, -442841, 0]], ![![73, -33537, -1118], ![-275, 125214, 0]]]
    h := ![![![167615, -3683, 4], ![583160, -665, 0]], ![![60399, -1306, 1], ![210138, -166, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {112} * I167N1 =  Ideal.span {B.equivFun.symm ![25, 19, 3]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E167RS1 


noncomputable def E167RS2 : RelationCertificate Table 28 ![![167, 0, 0], ![-29, 1, 0]]
  ![53, -37, 3] ![![28, 0, 0], ![2, 1, 0]] where
    su := ![![4676, 0, 0], ![-812, 28, 0]]
    hsu := by decide
    w := ![![1484, -1036, 84], ![364, -168, -28]]
    hw := by decide
    g := ![![![-102, 1001, 500], ![45, -14055, 0]], ![![15, -165, -82], ![16, 2305, 0]]]
    h := ![![![44930, -1578, 1], ![258733, -164, 0]], ![![11014, -380, 0], ![63425, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N2 : Ideal.span {28} * I167N2 =  Ideal.span {B.equivFun.symm ![53, -37, 3]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E167RS2 


noncomputable def E173RS1 : RelationCertificate Table 2 ![![173, 0, 0], ![34, 1, 0]]
  ![33, -21, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![346, 0, 0], ![68, 2, 0]]
    hsu := by decide
    w := ![![66, -42, 2], ![86, -16, -20]]
    hw := by decide
    g := ![![![-5474, -62, -112051], ![-31, 223884, 0]], ![![-1130, -13, -22480], ![-6, 44915, 0]]]
    h := ![![![317, 9, 0], ![-1612, 1, 0]], ![![411, -20, -1], ![-2090, 163, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {2} * I173N1 =  Ideal.span {B.equivFun.symm ![33, -21, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E173RS1 


noncomputable def E181RS0 : RelationCertificate Table 8 ![![181, 0, 0], ![4, 1, 0]]
  ![-145, -3, -3] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![1448, 0, 0], ![32, 8, 0]]
    hsu := by decide
    w := ![![-1160, -24, -24], ![32, 8, 0]]
    hw := by decide
    g := ![![![-73097, -2485214, 1260881], ![-292375, -10087051, 0]], ![![-2014, -68479, 34743], ![-8055, -277944, 0]]]
    h := ![![![-4353, -1092, -1], ![196937, 178, 0]], ![![116, 29, 0], ![-5248, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N0 : Ideal.span {8} * I181N0 =  Ideal.span {B.equivFun.symm ![-145, -3, -3]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E181RS0 


noncomputable def E181RS1 : RelationCertificate Table 56 ![![181, 0, 0], ![49, 1, 0]]
  ![23857, 339, 475] ![![56, 0, 0], ![-26, 1, 0]] where
    su := ![![10136, 0, 0], ![2744, 56, 0]]
    hsu := by decide
    w := ![![1335992, 18984, 26600], ![-579432, -8232, -11536]]
    hw := by decide
    g := ![![![302556677, 44359459498, -1706580627], ![651660516, 95568515103, 0]], ![![80236026, 11763834772, -452573876], ![172816051, 25344137052, 0]]]
    h := ![![![41005523, 927613, 1855], ![-151468894, -335280, 0]], ![![-17784507, -402338, -805], ![65693580, 145499, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {56} * I181N1 =  Ideal.span {B.equivFun.symm ![23857, 339, 475]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E181RS1 


noncomputable def E181RS2 : RelationCertificate Table 112 ![![181, 0, 0], ![-54, 1, 0]]
  ![-75, 55, -9] ![![112, 0, 0], ![30, 1, 0]] where
    su := ![![20272, 0, 0], ![-6048, 112, 0]]
    hsu := by decide
    w := ![![-8400, 6160, -1008], ![-3024, 2016, -224]]
    hw := by decide
    g := ![![![110, -70302, -2344], ![-497, 262476, 0]], ![![-56, 20544, 685], ![234, -76705, 0]]]
    h := ![![![-1749, 84, -1], ![-5861, 172, 0]], ![![-621, 65, -1], ![-2081, 179, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N2 : Ideal.span {112} * I181N2 =  Ideal.span {B.equivFun.symm ![-75, 55, -9]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E181RS2 


noncomputable def E191RS0 : RelationCertificate Table 28 ![![191, 0, 0], ![9, 1, 0]]
  ![83, -3, 1] ![![28, 0, 0], ![2, 1, 0]] where
    su := ![![5348, 0, 0], ![252, 28, 0]]
    hsu := by decide
    w := ![![2324, -84, 28], ![252, 28, 0]]
    hw := by decide
    g := ![![![10097135, -3978271213, -1991659890], ![-141359864, 55766476919, 0]], ![![422736, -166558468, -83384918], ![-5918303, 2334777704, 0]]]
    h := ![![![316, 35, 0], ![-6697, 1, 0]], ![![18, 2, 0], ![-381, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N0 : Ideal.span {28} * I191N0 =  Ideal.span {B.equivFun.symm ![83, -3, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E191RS0 


noncomputable def E191RS2 : RelationCertificate Table 112 ![![191, 0, 0], ![-34, 1, 0]]
  ![569, -365, 19] ![![112, 0, 0], ![30, 1, 0]] where
    su := ![![21392, 0, 0], ![-3808, 112, 0]]
    hsu := by decide
    w := ![![63728, -40880, 2128], ![18704, -11312, 224]]
    hw := by decide
    g := ![![![-1281, 344566, 11476], ![2792, -1286501, 0]], ![![197, -61939, -2063], ![-399, 231257, 0]]]
    h := ![![![2446693, -73898, 57], ![13744641, -10868, 0]], ![![718075, -21664, 16], ![4033887, -3054, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N2 : Ideal.span {112} * I191N2 =  Ideal.span {B.equivFun.symm ![569, -365, 19]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E191RS2 
