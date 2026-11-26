import IdealArithmetic.Examples.NF3_1_780332_1.PrimesBelow3_1_780332_1F4
import IdealArithmetic.Examples.NF3_1_780332_1.ClassGroupData3_1_780332_1

set_option linter.all false

noncomputable section


noncomputable def E197RS0 : RelationCertificate Table 9 ![![197, 0, 0], ![48, 1, 0]]
  ![-21969, -6581, -509] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![1773, 0, 0], ![432, 9, 0]]
    hsu := by decide
    w := ![![-197721, -59229, -4581], ![-196146, -58761, -4545]]
    hw := by decide
    g := ![![![292569, 7075517, -1787088], ![656138, 16083648, 0]], ![![73680, 1782909, -450317], ![165360, 4052824, 0]]]
    h := ![![![-341949, -7655, -13], ![1402958, 2052, 0]], ![![-339226, -7599, -13], ![1391786, 2056, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N0 : Ideal.span {9} * I197N0 =  Ideal.span {B.equivFun.symm ![-21969, -6581, -509]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E197RS0 


noncomputable def E197RS1 : RelationCertificate Table 531441 ![![197, 0, 0], ![-37, 1, 0]]
  ![13856895, 4151057, 321065] ![![531441, 0, 0], ![163602, 167, 1]] where
    su := ![![104693877, 0, 0], ![-19663317, 531441, 0]]
    hsu := by decide
    w := ![![7364122135695, 2206041883137, 170627104665], ![2299250788686, 688777828137, 53273771604]]
    hw := by decide
    g := ![![![-138915, 300653, 306], ![454576, -976360, 0]], ![![-23139, -1835, -2], ![75145, 5880, 0]]]
    h := ![![![55565045, -1517829, 2685], ![295471810, -207880, 0]], ![![17348748, -473891, 838], ![92253430, -64842, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {531441} * I197N1 =  Ideal.span {B.equivFun.symm ![13856895, 4151057, 321065]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E197RS1 


noncomputable def E197RS2 : RelationCertificate Table 81 ![![197, 0, 0], ![-11, 1, 0]]
  ![63, 26, 2] ![![81, 0, 0], ![-3180, -266, 38]] where
    su := ![![15957, 0, 0], ![-891, 81, 0]]
    hsu := by decide
    w := ![![5103, 2106, 162], ![54108, -486, -1458]]
    hw := by decide
    g := ![![![-3393, 31116, 1680], ![70087, 10524, 0]], ![![1979, -1565, -114], ![-3817, -580, 0]]]
    h := ![![![91, -8, 0], ![1624, 2, 0]], ![![762, -59, -1], ![13586, 179, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N2 : Ideal.span {81} * I197N2 =  Ideal.span {B.equivFun.symm ![63, 26, 2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E197RS2 


noncomputable def E199RS1 : RelationCertificate Table 6561 ![![199, 0, 0], ![-69, 1, 0]]
  ![1342989, 402320, 31118] ![![6561, 0, 0], ![-189639, -11761, 2308]] where
    su := ![![1305639, 0, 0], ![-452709, 6561, 0]]
    hsu := by decide
    w := ![![8811350829, 2639621520, 204165198], ![59234184225, 17744690331, 1372469346]]
    hw := by decide
    g := ![![![366825, 10717134, 2503946], ![-28550582, -4205964, 0]], ![![43408, -3665264, -860862], ![9798123, 1442560, 0]]]
    h := ![![![48368598, -753359, 946], ![139478377, -157136, 0]], ![![325156852, -5064754, 6364], ![937640367, -1057250, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {6561} * I199N1 =  Ideal.span {B.equivFun.symm ![1342989, 402320, 31118]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E199RS1 


noncomputable def E211RS1 : RelationCertificate Table 3 ![![211, 0, 0], ![-96, 1, 0]]
  ![219, 65, 5] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![633, 0, 0], ![-288, 3, 0]]
    hsu := by decide
    w := ![![657, 195, 15], ![2571, 774, 60]]
    hw := by decide
    g := ![![![-17449, -173163, 190436], ![-51904, -571298, 0]], ![![7778, 77091, -84779], ![23106, 254332, 0]]]
    h := ![![![1977, -18, 0], ![4343, 5, 0]], ![![7427, -67, 0], ![16315, 20, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {3} * I211N1 =  Ideal.span {B.equivFun.symm ![219, 65, 5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E211RS1 


noncomputable def E223RS1 : RelationCertificate Table 2187 ![![223, 0, 0], ![-71, 1, 0]]
  ![549, 5, -10] ![![2187, 0, 0], ![-36000, -3182, 422]] where
    su := ![![487701, 0, 0], ![-155277, 2187, 0]]
    hsu := by decide
    w := ![![1200663, 10935, -21870], ![-831060, -74358, 52488]]
    hw := by decide
    g := ![![![150933, -424483, -42931], ![-1387151, -213472, 0]], ![![-24319, 136988, 13366], ![442264, 67840, 0]]]
    h := ![![![5955, -87, 0], ![18696, -10, 0]], ![![-4014, 64, 0], ![-12602, 24, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {2187} * I223N1 =  Ideal.span {B.equivFun.symm ![549, 5, -10]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E223RS1 


noncomputable def E227RS1 : RelationCertificate Table 9 ![![227, 0, 0], ![-1, 1, 0]]
  ![171, 52, 4] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![2043, 0, 0], ![-9, 9, 0]]
    hsu := by decide
    w := ![![1539, 468, 36], ![1548, 459, 36]]
    hw := by decide
    g := ![![![-99, -801, 202], ![-43, -1814, 0]], ![![5, -1, 0], ![8, 0, 0]]]
    h := ![![![2, -1, 0], ![283, 4, 0]], ![![2, -1, 0], ![282, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {9} * I227N1 =  Ideal.span {B.equivFun.symm ![171, 52, 4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E227RS1 


noncomputable def E233RS0 : RelationCertificate Table 6561 ![![233, 0, 0], ![32, 1, 0]]
  ![125289, 6962, -1288] ![![6561, 0, 0], ![-504, 5, 1]] where
    su := ![![1528713, 0, 0], ![209952, 6561, 0]]
    hsu := by decide
    w := ![![822021129, 45677682, -8450568], ![-62854380, -3536379, 649539]]
    hw := by decide
    g := ![![![138640151009, -94967177741, 1251309881], ![-10722174401, -1639824380764, 0]], ![![19880513984, -13617961977, 179433472], ![-1537522694, -235145095452, 0]]]
    h := ![![![826337, 26333, 10], ![-6012851, -3618, 0]], ![![-63244, -2023, -1], ![460196, 332, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N0 : Ideal.span {6561} * I233N0 =  Ideal.span {B.equivFun.symm ![125289, 6962, -1288]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E233RS0 


noncomputable def E233RS1 : RelationCertificate Table 729 ![![233, 0, 0], ![72, 1, 0]]
  ![-63, 25, 4] ![![729, 0, 0], ![12834, 725, -152]] where
    su := ![![169857, 0, 0], ![52488, 729, 0]]
    hsu := by decide
    w := ![![-45927, 18225, 2916], ![-1310742, -175689, 3645]]
    hw := by decide
    g := ![![![1216200447, 7268392453, 1631524263], ![28299564184, 4292624232, 0]], ![![400202550, 2391735969, 536869097], ![9312249762, 1412530196, 0]]]
    h := ![![![-1877895, -30115, -56], ![6077076, 13052, 0]], ![![-53713910, -860293, -1587], ![173824156, 369776, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {729} * I233N1 =  Ideal.span {B.equivFun.symm ![-63, 25, 4]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E233RS1 


noncomputable def E233RS2 : RelationCertificate Table 59049 ![![233, 0, 0], ![-104, 1, 0]]
  ![-186147, -24635, 3019] ![![59049, 0, 0], ![-13545, 167, 1]] where
    su := ![![13758417, 0, 0], ![-6141096, 59049, 0]]
    hsu := by decide
    w := ![![-10991794203, -1454672115, 178268931], ![2788943319, 363741840, -44818191]]
    hw := by decide
    g := ![![![-1215338942396, 31256012465270, -388943517695], ![367171917229, 137523105414944, 0]], ![![538886740965, -13859056045048, 172459299344], ![-162805649431, -60978361444624, 0]]]
    h := ![![![-1347176135539, 14779665938, -17558154], ![-3018192686485, 4091052901, 0]], ![![341820212303, -3750055409, 4455022], ![765808744417, -1038020885, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N2 : Ideal.span {59049} * I233N2 =  Ideal.span {B.equivFun.symm ![-186147, -24635, 3019]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E233RS2 


noncomputable def E239RS0 : RelationCertificate Table 81 ![![239, 0, 0], ![-106, 1, 0]]
  ![34731, 3998, -517] ![![81, 0, 0], ![-3180, -266, 38]] where
    su := ![![19359, 0, 0], ![-8586, 81, 0]]
    hsu := by decide
    w := ![![2813211, 323838, -41877], ![51066288, 2976750, -535734]]
    hw := by decide
    g := ![![![-16683, 121178, 6225], ![281495, 42220, 0]], ![![8412, -53559, -2788], ![-124165, -18630, 0]]]
    h := ![![![2452183, -25783, 23], ![5528651, -6014, 0]], ![![44517376, -469582, 442], ![100368136, -112252, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N0 : Ideal.span {81} * I239N0 =  Ideal.span {B.equivFun.symm ![34731, 3998, -517]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E239RS0 


noncomputable def E239RS1 : RelationCertificate Table 81 ![![239, 0, 0], ![-68, 1, 0]]
  ![-3231, -319, 44] ![![81, 0, 0], ![-3180, -266, 38]] where
    su := ![![19359, 0, 0], ![-5508, 81, 0]]
    hsu := by decide
    w := ![![-261711, -25839, 3564], ![-3020328, -147582, 29484]]
    hw := by decide
    g := ![![![9693, -54103, -2985], ![-122441, -18400, 0]], ![![-1902, 15389, 835], ![34691, 5210, 0]]]
    h := ![![![-135457, 2139, -2], ![-476044, 522, 0]], ![![-1564024, 24386, -19], ![-5496536, 4905, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {81} * I239N1 =  Ideal.span {B.equivFun.symm ![-3231, -319, 44]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E239RS1 


noncomputable def E239RS2 : RelationCertificate Table 59049 ![![239, 0, 0], ![-65, 1, 0]]
  ![-133551, -11327, 1675] ![![59049, 0, 0], ![-504, 5, 1]] where
    su := ![![14112711, 0, 0], ![-3838185, 59049, 0]]
    hsu := by decide
    w := ![![-7886052999, -668848023, 98907075], ![65662488, 5609655, -826686]]
    hw := by decide
    g := ![![![-6310923238043, 4298071959507, -56554557198], ![54228511216, 667887163893572, 0]], ![![1712128840793, -1166050145584, 15343030613], ![-14711950570, -181195180543048, 0]]]
    h := ![![![-5237079, 84935, -61], ![-19254282, 16254, 0]], ![![43658, -675, 0], ![160510, -14, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N2 : Ideal.span {59049} * I239N2 =  Ideal.span {B.equivFun.symm ![-133551, -11327, 1675]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E239RS2 


noncomputable def E241RS1 : RelationCertificate Table 27 ![![241, 0, 0], ![19, 1, 0]]
  ![-189, -10, 2] ![![27, 0, 0], ![-402, -32, 5]] where
    su := ![![6507, 0, 0], ![513, 27, 0]]
    hsu := by decide
    w := ![![-5103, -270, 54], ![12366, 1512, -189]]
    hw := by decide
    g := ![![![-745, 234, -184], ![13358, 1932, 0]], ![![241, 45, -20], ![1196, 170, 0]]]
    h := ![![![-83692, -4443, -2], ![1061557, 484, 0]], ![![202736, 10728, 3], ![-2571522, -730, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {27} * I241N1 =  Ideal.span {B.equivFun.symm ![-189, -10, 2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E241RS1 
