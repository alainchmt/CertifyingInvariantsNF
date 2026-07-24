import IdealArithmetic.Examples.NF3_1_959175_1.PrimesBelow3_1_959175_1F2
import IdealArithmetic.Examples.NF3_1_959175_1.ClassGroupData3_1_959175_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 4 ![![83, 0, 0], ![-1, 1, 0]]
  ![-40276844, -11716348, -1765431] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![332, 0, 0], ![-4, 4, 0]]
    hsu := by decide
    w := ![![-161107376, -46865392, -7061724], ![-534597524, -155511952, -23432696]]
    hw := by decide
    g := ![![![-76800, -26027, -25045], ![-25703, 54366, 0]], ![![7721, 174, 153], ![1977, -663, 0]]]
    h := ![![![-970426, 344002, -21259], ![-40268514, -467, 0]], ![![-3220134, 1141491, -70540], ![-133621741, -1677, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {4} * I83N1 =  Ideal.span {B.equivFun.symm ![-40276844, -11716348, -1765431]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E83RS1 


noncomputable def E89RS0 : RelationCertificate Table 2 ![![89, 0, 0], ![38, 1, 0]]
  ![-4266, -1241, -187] ![![2, 0, 0], ![-35, -1, 1]] where
    su := ![![178, 0, 0], ![76, 2, 0]]
    hsu := by decide
    w := ![![-8532, -2482, -374], ![-93450, -27184, -4096]]
    hw := by decide
    g := ![![![-6724, -65588, -40625], ![130291, 16330, 0]], ![![-3053, -29935, -18547], ![59476, 7455, 0]]]
    h := ![![![-291718, -9033, -71], ![683122, 3066, 0]], ![![-3194615, -98657, -764], ![7480895, 32974, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {2} * I89N0 =  Ideal.span {B.equivFun.symm ![-4266, -1241, -187]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![-20, 1, 0]]
  ![-26, -7, -1] ![![2, 0, 0], ![-35, -1, 1]] where
    su := ![![178, 0, 0], ![-40, 2, 0]]
    hsu := by decide
    w := ![![-52, -14, -2], ![-490, -148, -24]]
    hw := by decide
    g := ![![![-18439, -179441, -111299], ![356785, 44730, 0]], ![![3980, 38452, 23849], ![-76452, -9585, 0]]]
    h := ![![![-954, 57, -1], ![-4244, 44, 0]], ![![-9205, 477, -2], ![-40950, 83, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![-26, -7, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 2 ![![89, 0, 0], ![-18, 1, 0]]
  ![110156346, 8554739, -3110099] ![![2, 0, 0], ![-35, -1, 1]] where
    su := ![![178, 0, 0], ![-36, 2, 0]]
    hsu := by decide
    w := ![![220312692, 17109478, -6220198], ![281510250, -166106660, 25400248]]
    hw := by decide
    g := ![![![-480736455561, 58629191594641, 16199724988271], ![-12801845330449, -51830, 0]], ![![30934179042, -3772641059314, -1042411579302], ![823766606914, 10295, 0]]]
    h := ![![![274426614, -15302295, -8915], ![1350767350, -1158332, 0]], ![![352296951, -20662157, 171496], ![1734092973, -1281510, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {2} * I89N2 =  Ideal.span {B.equivFun.symm ![110156346, 8554739, -3110099]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E89RS2 


noncomputable def E97RS1 : RelationCertificate Table 4 ![![97, 0, 0], ![-9, 1, 0]]
  ![-11694156, -3401776, -512583] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![388, 0, 0], ![-36, 4, 0]]
    hsu := by decide
    w := ![![-46776624, -13607104, -2050332], ![-155217396, -45152024, -6803552]]
    hw := by decide
    g := ![![![-48071, 350, 1205], ![-11929, 0, 0]], ![![7740, -142, -182], ![1901, 7, 0]]]
    h := ![![![-403825632, 45102164, -75563], ![-4351043572, 3408514, 0]], ![![-1340001858, 149661079, -250736], ![-14437930653, 11310252, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {4} * I97N1 =  Ideal.span {B.equivFun.symm ![-11694156, -3401776, -512583]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E97RS1 


noncomputable def E107RS1 : RelationCertificate Table 4 ![![107, 0, 0], ![-17, 1, 0]]
  ![8852, 2575, 388] ![![4, 0, 0], ![-69, -3, 2]] where
    su := ![![428, 0, 0], ![-68, 4, 0]]
    hsu := by decide
    w := ![![35408, 10300, 1552], ![288012, 83780, 12624]]
    hw := by decide
    g := ![![![41, 4, -16], ![125, 0, 0]], ![![61, -1, 2], ![-23, 0, 0]]]
    h := ![![![608514, -36457, 90], ![3829538, -4621, 0]], ![![4949623, -296571, 736], ![31149274, -37798, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {4} * I107N1 =  Ideal.span {B.equivFun.symm ![8852, 2575, 388]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E107RS1 


noncomputable def E113RS0 : RelationCertificate Table 4 ![![113, 0, 0], ![19, 1, 0]]
  ![-58564, -17036, -2567] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![452, 0, 0], ![76, 4, 0]]
    hsu := by decide
    w := ![![-234256, -68144, -10268], ![-777324, -226120, -34072]]
    hw := by decide
    g := ![![![3526, -129, -69], ![853, 0, 0]], ![![431, -14, -13], ![107, 7, 0]]]
    h := ![![![-56690, -3210, -33], ![334074, 581, 0]], ![![-188025, -10612, -106], ![1108026, 1730, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {4} * I113N0 =  Ideal.span {B.equivFun.symm ![-58564, -17036, -2567]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 4 ![![113, 0, 0], ![25, 1, 0]]
  ![636, 44, -17] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![452, 0, 0], ![100, 4, 0]]
    hsu := by decide
    w := ![![2544, 176, -68], ![-4124, -160, 88]]
    hw := by decide
    g := ![![![-3051, -721, -144], ![-939, 0, 0]], ![![-1007, -235, -44], ![-307, -7, 0]]]
    h := ![![![37372, 1614, 9], ![-168896, -517, 0]], ![![-60662, -2637, -16], ![274151, 915, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {4} * I113N1 =  Ideal.span {B.equivFun.symm ![636, 44, -17]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 4 ![![113, 0, 0], ![-44, 1, 0]]
  ![5036, -1532, 199] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![452, 0, 0], ![-176, 4, 0]]
    hsu := by decide
    w := ![![20144, -6128, 796], ![60756, 12320, -3064]]
    hw := by decide
    g := ![![![-5936115, -1401589, -280296], ![-1834423, 0, 0]], ![![1666678, 393519, 78695], ![515052, 7, 0]]]
    h := ![![![506388, -11591, 5], ![1300382, -183, 0]], ![![1519741, -34784, 6], ![3902626, -722, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {4} * I113N2 =  Ideal.span {B.equivFun.symm ![5036, -1532, 199]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E113RS2 


noncomputable def E127RS1 : RelationCertificate Table 4 ![![127, 0, 0], ![-2, 1, 0]]
  ![164, -19, 1] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![508, 0, 0], ![-8, 4, 0]]
    hsu := by decide
    w := ![![656, -76, 4], ![116, 216, -40]]
    hw := by decide
    g := ![![![-1489, -513, -64013], ![247, 127890, 0]], ![![-120, -42, 502], ![22, -1015, 0]]]
    h := ![![![2, 81, -163], ![45, 10351, 0]], ![![1, 14, -28], ![49, 1773, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {4} * I127N1 =  Ideal.span {B.equivFun.symm ![164, -19, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E127RS1 


noncomputable def E131RS0 : RelationCertificate Table 4 ![![131, 0, 0], ![14, 1, 0]]
  ![684, 199, 30] ![![4, 0, 0], ![-69, -3, 2]] where
    su := ![![524, 0, 0], ![56, 4, 0]]
    hsu := by decide
    w := ![![2736, 796, 120], ![22244, 6476, 976]]
    hw := by decide
    g := ![![![12, 1, 4], ![-37, 0, 0]], ![![4, 1, 0], ![-2, 0, 0]]]
    h := ![![![35792, 2586, 4], ![-334862, -247, 0]], ![![291111, 21074, 38], ![-2723570, -2367, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {4} * I131N0 =  Ideal.span {B.equivFun.symm ![684, 199, 30]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E131RS0 


noncomputable def E131RS1 : RelationCertificate Table 2 ![![131, 0, 0], ![51, 1, 0]]
  ![-13371906, 2129287, -184467] ![![2, 0, 0], ![-35, -1, 1]] where
    su := ![![262, 0, 0], ![102, 2, 0]]
    hsu := by decide
    w := ![![-26743812, 4258574, -368934], ![1167518590, 36003544, -23264640]]
    hw := by decide
    g := ![![![-68895491076, 8402286697900, 2321620436303], ![-1834662036363, 47070, 0]], ![![-33276559611, 4058309223951, 1121343987553], ![-886142824517, 19351, 0]]]
    h := ![![![-62439930, -1458331, -11111], ![160122724, 635537, 0]], ![![2740169473, 64676660, 330350], ![-7027028268, -27454085, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {2} * I131N1 =  Ideal.span {B.equivFun.symm ![-13371906, 2129287, -184467]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E131RS1 


noncomputable def E131RS2 : RelationCertificate Table 2 ![![131, 0, 0], ![-65, 1, 0]]
  ![-2457894, 238466, -6777] ![![2, 0, 0], ![-35, -2, 1]] where
    su := ![![262, 0, 0], ![-130, 2, 0]]
    hsu := by decide
    w := ![![-4915788, 476932, -13554], ![158489450, 8425008, -3785764]]
    hw := by decide
    g := ![![![4448206531, -130292934972, -40563497365], ![32167572265, 0, 0]], ![![-1790383610, 52442335599, 16326630001], ![-12947306905, 3, 0]]]
    h := ![![![-344094, -108271854, 3383657], ![-655668, -221632922, 0]], ![![10335690, 3240876005, -101295498], ![19611241, 6633908678, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {2} * I131N2 =  Ideal.span {B.equivFun.symm ![-2457894, 238466, -6777]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E131RS2 


noncomputable def E137RS0 : RelationCertificate Table 2 ![![137, 0, 0], ![-57, 1, 0]]
  ![993694, 289061, 43556] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![274, 0, 0], ![-114, 2, 0]]
    hsu := by decide
    w := ![![1987388, 578122, 87112], ![13189374, 3836728, 578122]]
    hw := by decide
    g := ![![![12365, -483, -663], ![5941, 0, 0]], ![![-6254, 325, 317], ![-2963, 0, 0]]]
    h := ![![![114530222, -2279339, 10042], ![275256960, -666099, 0]], ![![760083675, -15127160, 66653], ![1826752084, -4421200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {2} * I137N0 =  Ideal.span {B.equivFun.symm ![993694, 289061, 43556]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 4 ![![137, 0, 0], ![-50, 1, 0]]
  ![1812, -18, -23] ![![4, 0, 0], ![-33, -2, 1]] where
    su := ![![548, 0, 0], ![-200, 4, 0]]
    hsu := by decide
    w := ![![7248, -72, -92], ![-45516, -4160, 1396]]
    hw := by decide
    g := ![![![582175, 34954, 471224], ![-4702543, -562830, 0]], ![![2933971352, 199304348, 2382055503], ![-23709401834, -2836236157, 0]]]
    h := ![![![323476, -7184, 29], ![886288, -1998, 0]], ![![-2031017, 45206, -185], ![-5564759, 12847, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {4} * I137N1 =  Ideal.span {B.equivFun.symm ![1812, -18, -23]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 4 ![![137, 0, 0], ![-30, 1, 0]]
  ![573708, 166889, 25147] ![![4, 0, 0], ![35, 3, -1]] where
    su := ![![548, 0, 0], ![-120, 4, 0]]
    hsu := by decide
    w := ![![2294832, 667556, 100588], ![1515500, 440852, 66428]]
    hw := by decide
    g := ![![![-1237836, 2676081, -242818], ![-8763101, -1113028, 0]], ![![265565, -574194, 52100], ![1880314, 238819, 0]]]
    h := ![![![6040944, -205799, 583], ![27567854, -27362, 0]], ![![3989455, -135910, 385], ![18205882, -18069, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {4} * I137N2 =  Ideal.span {B.equivFun.symm ![573708, 166889, 25147]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E137RS2 
