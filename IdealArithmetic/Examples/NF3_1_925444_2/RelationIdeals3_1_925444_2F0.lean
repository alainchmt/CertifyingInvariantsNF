import IdealArithmetic.Examples.NF3_1_925444_2.PrimesBelow3_1_925444_2F0
import IdealArithmetic.Examples.NF3_1_925444_2.ClassGroupData3_1_925444_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![0, 1, 0]]
  ![610360, -11450, -9783] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![4, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![1220720, -22900, -19566], ![-1636396, 262954, -57250]]
    hw := by decide
    g := ![![![-9146863435, -337825859, -806997878], ![-4742344646, 3, 0]], ![![-72188965340, -2666192518, -6368996501], ![-37427578927, -3, 0]]]
    h := ![![![277401, -56120, 64556], ![156348, -27779, 0]], ![![-357158, -32220, -144165], ![92035, 51941, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![610360, -11450, -9783]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![3, -3, -5], ![0, 2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![3, -3, -5], ![0, 2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0], ![-21, -1, 1]]
  ![39621, -6319, 1369] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![27, 0, 0], ![-189, -9, 9]]
    hsu := by decide
    w := ![![356589, -56871, 12321], ![211383, 89748, -37071]]
    hw := by decide
    g := ![![![5946021, 1737505, 458379], ![-1788948, 4, 0]], ![![14134463, 4130272, 1089650], ![-4252560, -32, 0]]]
    h := ![![![446, -2714, 1064], ![-1823, 0, 0]], ![![-25, 2950, -999], ![-1122, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![39621, -6319, 1369]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![-3, 3, 10], ![3, -6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-3, 3, 10], ![3, -6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 18 ![![5, 0, 0], ![-23, -1, 1]]
  ![-2500134, -588022, -175169] ![![18, 0, 0], ![-3, 1, 0]] where
    su := ![![90, 0, 0], ![-414, -18, 18]]
    hsu := by decide
    w := ![![-45002412, -10584396, -3153042], ![-31962762, -7517520, -2239434]]
    hw := by decide
    g := ![![![174644208844076064318, 90665217148762306222, -446639860290362983387], ![-24070411632414771469, 1607903497045306740208, 0]], ![![-803363360782721718180, -417059998936206222413, 2054543357591340388316], ![110723893522886607343, -7396356087328825398313, 0]]]
    h := ![![![-850236842, 212210032, -290900649], ![3810467440, 392689894, 0]], ![![-603876910, 150721227, -206610886], ![2706367469, 278906242, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {18} * I5N0 =  Ideal.span {B.equivFun.symm ![-2500134, -588022, -175169]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 18 ![![5, 0, 0], ![-22, -1, 1]]
  ![18582, -56, -403] ![![18, 0, 0], ![-3, 1, 0]] where
    su := ![![90, 0, 0], ![-396, -18, 18]]
    hsu := by decide
    w := ![![334476, -1008, -7254], ![-149130, 5742, 1332]]
    hw := by decide
    g := ![![![-242123, -99775, 366279], ![34823, -1343487, 0]], ![![494917, 288719, -1575880], ![-66430, 5642655, 0]]]
    h := ![![![131472, -23627, 45856], ![-564495, -55802, 0]], ![![-59305, 10717, -20708], ![254658, 25174, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {18} * I5N1 =  Ideal.span {B.equivFun.symm ![18582, -56, -403]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 18 ![![5, 0, 0], ![2, 1, 0]]
  ![-6785634, -378662, 290615] ![![18, 0, 0], ![-3, 1, 0]] where
    su := ![![90, 0, 0], ![36, 18, 0]]
    hsu := by decide
    w := ![![-122141412, -6815916, 5231070], ![88536906, 2892708, -3055770]]
    hw := by decide
    g := ![![![-13593478843, -3393942731, -976668715], ![2077027447, 11326, 0]], ![![297377834256, 167410345408, -887648775095], ![-40262397618, 3183029600525, 0]]]
    h := ![![![-796038704, -61782089, -3937525], ![-330771897, 0, 19978240]], ![![581554539, 45114063, 2885136], ![241644631, 0, -14595445]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {18} * I5N2 =  Ideal.span {B.equivFun.symm ![-6785634, -378662, 290615]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![-23, 1, 1]]
  ![3594650, 845448, 251855] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![14, 0, 0], ![-46, 2, 2]]
    hsu := by decide
    w := ![![7189300, 1690896, 503710], ![60334114, 14190354, 4227240]]
    hw := by decide
    g := ![![![2857, -404, 90], ![1227, -81, 0]], ![![-8009, 868, -262], ![-3569, 270, 0]]]
    h := ![![![51389, 140871, 56072], ![-140649, 0, 0]], ![![431129, 1182225, 470574], ![-1180398, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![3594650, 845448, 251855]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 4 ![![7, 0, 0], ![3, 1, 0]]
  ![44, 0, -1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![28, 0, 0], ![12, 4, 0]]
    hsu := by decide
    w := ![![176, 0, -4], ![-188, 12, 0]]
    hw := by decide
    g := ![![![-1, 17, 27], ![5, -21, 0]], ![![22, 10, 12], ![11, -8, 0]]]
    h := ![![![1658, -4258, -4243], ![106, 5940, 0]], ![![-1796, 4606, 4590], ![-109, -6426, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {4} * I7N1 =  Ideal.span {B.equivFun.symm ![44, 0, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 6 ![![11, 0, 0], ![-21, -6, 1]]
  ![582, 578, -221] ![![6, 0, 0], ![3, 1, 0]] where
    su := ![![66, 0, 0], ![-126, -36, 6]]
    hsu := by decide
    w := ![![3492, 3468, -1326], ![-50682, -3600, 2448]]
    hw := by decide
    g := ![![![-177339862, 460237209, 458246941], ![-11963725, -549898206, 0]], ![![332594160, -862927652, -859205741], ![22475811, 1031059138, 0]]]
    h := ![![![9, 40, -18], ![-23, 0, 0]], ![![-178, 114, 9], ![309, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {6} * I11N0 =  Ideal.span {B.equivFun.symm ![582, 578, -221]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 36 ![![11, 0, 0], ![-2, 1, 0]]
  ![-444, -104, -31] ![![36, 0, 0], ![-3, 1, 0]] where
    su := ![![396, 0, 0], ![-72, 36, 0]]
    hsu := by decide
    w := ![![-15984, -3744, -1116], ![-5652, -1332, -396]]
    hw := by decide
    g := ![![![13508515, 6819279, -33966357], ![-936269, 244557771, 0]], ![![-3682708, -1859082, 9259956], ![255260, -66671683, 0]]]
    h := ![![![147104, 2402, -379921], ![-26526, 835820, 0]], ![![52001, 849, -134301], ![-9376, 295460, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {36} * I11N1 =  Ideal.span {B.equivFun.symm ![-444, -104, -31]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 3 ![![13, 0, 0], ![4, 1, 0]]
  ![4308357, 172156, -159982] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![39, 0, 0], ![12, 3, 0]]
    hsu := by decide
    w := ![![12925071, 516468, -479946], ![-37460136, -466755, 1020762]]
    hw := by decide
    g := ![![![-160263201063, -33923965446, -11228655958], ![-11307988482, -56, 0]], ![![-243901109092, -51628151382, -17088649438], ![-17209383791, -16, 0]]]
    h := ![![![-516215, 2521030, 2079766], ![35094, -5439388, 0]], ![![863880, -5340187, -4423302], ![-144970, 11568636, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {3} * I13N0 =  Ideal.span {B.equivFun.symm ![4308357, 172156, -159982]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS0 


noncomputable def E17RS0 : RelationCertificate Table 9 ![![17, 0, 0], ![2, 1, 0]]
  ![-723, -110, 56] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![153, 0, 0], ![18, 9, 0]]
    hsu := by decide
    w := ![![-6507, -990, 504], ![15381, 1179, -774]]
    hw := by decide
    g := ![![![-3002, -861, -396], ![907, 288, 0]], ![![-3193, -932, -268], ![967, 38, 0]]]
    h := ![![![-109921, 219749, 274698], ![5, -933962, 0]], ![![262039, -523876, -654858], ![23, 2226500, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {9} * I17N0 =  Ideal.span {B.equivFun.symm ![-723, -110, 56]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 9 ![![17, 0, 0], ![3, 1, 0]]
  ![57, 2, -2] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![153, 0, 0], ![27, 9, 0]]
    hsu := by decide
    w := ![![513, 18, -18], ![-639, -9, 18]]
    hw := by decide
    g := ![![![-11, -9, 43], ![10, -77, 0]], ![![1, -1, 8], ![2, -14, 0]]]
    h := ![![![1, 4, 4], ![4, -14, 0]], ![![-5, -5, -4], ![14, 14, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {9} * I17N1 =  Ideal.span {B.equivFun.symm ![57, 2, -2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 9 ![![17, 0, 0], ![-6, 1, 0]]
  ![-646197, -240856, 101284] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![153, 0, 0], ![-54, 9, 0]]
    hsu := by decide
    w := ![![-5815773, -2167704, 911556], ![25918191, 2835747, -1609416]]
    hw := by decide
    g := ![![![4285713068760, 2468188832835, -11721699593818], ![-1154327819269, 21096827675518, 0]], ![![-1527536741631, -875488834232, 4135919319378], ![411902376749, -7445939177574, 0]]]
    h := ![![![-142072541, -308548716, 383321692], ![31993332, -1303273496, 0]], ![![645381637, 1401582106, -1741278532], ![-145335743, 5920311244, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {9} * I17N2 =  Ideal.span {B.equivFun.symm ![-646197, -240856, 101284]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E17RS2 


noncomputable def E19RS1 : RelationCertificate Table 4 ![![19, 0, 0], ![-6, 1, 0]]
  ![-103092, 1092, 1955] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![76, 0, 0], ![-24, 4, 0]]
    hsu := by decide
    w := ![![-412368, 4368, 7820], ![348284, -37256, 5460]]
    hw := by decide
    g := ![![![65467260, 11709096, 4925575], ![19294093, -570, 0]], ![![33713890, 6029467, 2535910], ![9935842, 195, 0]]]
    h := ![![![2051988, 4399796, -5472175], ![-416408, 20794656, 0]], ![![-1788713, -3835450, 4769890], ![363000, -18125309, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {4} * I19N1 =  Ideal.span {B.equivFun.symm ![-103092, 1092, 1955]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 36 ![![23, 0, 0], ![4, 1, 0]]
  ![146436, 3112, -4453] ![![36, 0, 0], ![-3, 1, 0]] where
    su := ![![828, 0, 0], ![144, 36, 0]]
    hsu := by decide
    w := ![![5271696, 112032, -160308], ![-1478628, 828, 33372]]
    hw := by decide
    g := ![![![-14064008, -7412710, 38405103], ![966095, -275919293, 0]], ![![-1638290, -1096283, 6736093], ![106098, -47985949, 0]]]
    h := ![![![-673980, 2056874, 1712749], ![-27774, -7879536, 0]], ![![189735, -578987, -482166], ![7830, 2218149, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {36} * I23N1 =  Ideal.span {B.equivFun.symm ![146436, 3112, -4453]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E23RS1 
