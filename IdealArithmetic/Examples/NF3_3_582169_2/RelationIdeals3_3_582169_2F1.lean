import IdealArithmetic.Examples.NF3_3_582169_2.PrimesBelow3_3_582169_2F1
import IdealArithmetic.Examples.NF3_3_582169_2.ClassGroupData3_3_582169_2

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 5125 ![![41, 0, 0], ![6, 1, 0]]
  ![-32734, 1767, 197] ![![5125, 0, 0], ![-62, 1, 0]] where
    su := ![![210125, 0, 0], ![30750, 5125, 0]]
    hsu := by decide
    w := ![![-167761750, 9055875, 1009625], ![1706625, -92250, -10250]]
    hw := by decide
    g := ![![![10, -2028516, 32718], ![865, -167679738, 0]], ![![4, -340318, 5489], ![344, -28131120, 0]]]
    h := ![![![-32654, -5385, -15], ![217680, 812, 0]], ![![327, 53, 0], ![-2179, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {5125} * I41N0 =  Ideal.span {B.equivFun.symm ![-32734, 1767, 197]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 125 ![![41, 0, 0], ![14, 1, 0]]
  ![2289, -107, -12] ![![125, 0, 0], ![-62, 1, 0]] where
    su := ![![5125, 0, 0], ![1750, 125, 0]]
    hsu := by decide
    w := ![![286125, -13375, -1500], ![-122250, 5875, 625]]
    hw := by decide
    g := ![![![3599774, 1130387025, -18232985], ![7257685, 2279123154, 0]], ![![1299105, 407930562, -6579863], ![2619208, 822482892, 0]]]
    h := ![![![2275, 160, 0], ![-6499, -12, 0]], ![![-982, -83, -1], ![2806, 46, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {125} * I41N1 =  Ideal.span {B.equivFun.symm ![2289, -107, -12]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 1 ![![41, 0, 0], ![20, 1, 0]]
  ![1, 0, 0] ![![41, 0, 0], ![20, 1, 0]] where
    su := ![![41, 0, 0], ![20, 1, 0]]
    hsu := by decide
    w := ![![41, 0, 0], ![20, 1, 0]]
    hw := by decide
    g := ![![![181, 9, 0], ![-369, 0, 0]], ![![60, 3, 0], ![-122, 0, 0]]]
    h := ![![![181, 9, 0], ![-369, 0, 0]], ![![60, 3, 0], ![-122, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {1} * I41N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E41RS2 


noncomputable def E43RS0 : RelationCertificate Table 41 ![![43, 0, 0], ![3, 1, 0]]
  ![486, -19, -3] ![![41, 0, 0], ![20, 1, 0]] where
    su := ![![1763, 0, 0], ![123, 41, 0]]
    hsu := by decide
    w := ![![19926, -779, -123], ![14637, -656, -82]]
    hw := by decide
    g := ![![![-224854, 23398478, 1170486], ![461033, -47989936, 0]], ![![-23024, 2396229, 119869], ![47224, -4914632, 0]]]
    h := ![![![53754, 18007, 31], ![-770312, -1336, 0]], ![![39486, 13228, 23], ![-565847, -991, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {41} * I43N0 =  Ideal.span {B.equivFun.symm ![486, -19, -3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 125 ![![43, 0, 0], ![15, 1, 0]]
  ![-3953, 214, 24] ![![125, 0, 0], ![-62, 1, 0]] where
    su := ![![5375, 0, 0], ![1875, 125, 0]]
    hsu := by decide
    w := ![![-494125, 26750, 3000], ![205750, -11125, -1250]]
    hw := by decide
    g := ![![![-243, -85058, 1372], ![-480, -171496, 0]], ![![-57, -32858, 530], ![-109, -66248, 0]]]
    h := ![![![-4923116, -381590, -3559], ![14112669, 153061, 0]], ![![2049932, 158876, 1481], ![-5876362, -63693, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {125} * I43N1 =  Ideal.span {B.equivFun.symm ![-3953, 214, 24]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 5125 ![![43, 0, 0], ![-19, 1, 0]]
  ![-18131, 853, 98] ![![5125, 0, 0], ![-62, 1, 0]] where
    su := ![![220375, 0, 0], ![-97375, 5125, 0]]
    hsu := by decide
    w := ![![-92921375, 4371625, 502250], ![963500, -46125, -5125]]
    hw := by decide
    g := ![![![-1244044112, -527102889236300, 8501659827444], ![-102834291438, -43571006615650471, 0]], ![![564150829, 239031324778145, -3855344094796], ![46633435445, 19758638485829494, 0]]]
    h := ![![![-2039941119, 122536407, -798476], ![-4616707894, 34334566, 0]], ![![21152388, -1270585, 8279], ![47871184, -355998, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {5125} * I43N2 =  Ideal.span {B.equivFun.symm ![-18131, 853, 98]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E43RS2 


noncomputable def E59RS0 : RelationCertificate Table 3125 ![![59, 0, 0], ![29, 1, 0]]
  ![21849, -1012, -117] ![![3125, 0, 0], ![-437, 1, 0]] where
    su := ![![184375, 0, 0], ![90625, 3125, 0]]
    hsu := by decide
    w := ![![68278125, -3162500, -365625], ![-9356250, 434375, 50000]]
    hw := by decide
    g := ![![![1256, 20191572, -46205], ![8955, 144390554, 0]], ![![567, 10136207, -23195], ![4037, 72484328, 0]]]
    h := ![![![464581636, 29302751, 458023], ![-945182575, -27023474, 0]], ![![-63661938, -4015399, -62764], ![129519012, 3703092, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {3125} * I59N0 =  Ideal.span {B.equivFun.symm ![21849, -1012, -117]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 128125 ![![59, 0, 0], ![-24, 1, 0]]
  ![-144944, 7372, 877] ![![128125, 0, 0], ![-41062, 1, 0]] where
    su := ![![7559375, 0, 0], ![-3075000, 128125, 0]]
    hsu := by decide
    w := ![![-18570950000, 944537500, 112365625], ![5950253125, -302631250, -36003125]]
    hw := by decide
    g := ![![![24291, -4976139514, 121186], ![75795, -15526956192, 0]], ![![7882, 1837237061, -44743], ![24594, 5732696860, 0]]]
    h := ![![![-588312562432, 27149008902, -109832712], ![-1446268376606, 6480130885, 0]], ![![188499168827, -8698718892, 35191114], ![463393788098, -2076276007, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {128125} * I59N1 =  Ideal.span {B.equivFun.symm ![-144944, 7372, 877]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 1025 ![![59, 0, 0], ![-6, 1, 0]]
  ![-2668, 134, 19] ![![1025, 0, 0], ![-62, 1, 0]] where
    su := ![![60475, 0, 0], ![-6150, 1025, 0]]
    hsu := by decide
    w := ![![-2734700, 137350, 19475], ![134275, -6150, -1025]]
    hw := by decide
    g := ![![![-19, -1202057, 19388], ![-374, -19872720, 0]], ![![58, 99261, -1601], ![956, 1641024, 0]]]
    h := ![![![-3200, 536, -1], ![-31022, 78, 0]], ![![169, -28, 0], ![1640, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {1025} * I59N2 =  Ideal.span {B.equivFun.symm ![-2668, 134, 19]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E59RS2 


noncomputable def E61RS0 : RelationCertificate Table 25625 ![![61, 0, 0], ![1, 1, 0]]
  ![-12411, 243, 88] ![![25625, 0, 0], ![10188, 1, 0]] where
    su := ![![1563125, 0, 0], ![25625, 25625, 0]]
    hsu := by decide
    w := ![![-318031875, 6226875, 2255000], ![-126587500, 2485625, 896875]]
    hw := by decide
    g := ![![![17186, -1878697750, -184403], ![-43226, 4725326844, 0]], ![![-3905, -65682034, -6447], ![9822, 165204369, 0]]]
    h := ![![![-408, -201, 1], ![12477, 27, 0]], ![![-162, -80, 0], ![4942, 35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {25625} * I61N0 =  Ideal.span {B.equivFun.symm ![-12411, 243, 88]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 205 ![![61, 0, 0], ![2, 1, 0]]
  ![-853, 39, 4] ![![205, 0, 0], ![-62, 1, 0]] where
    su := ![![12505, 0, 0], ![410, 205, 0]]
    hsu := by decide
    w := ![![-174865, 7995, 820], ![46330, -2255, -205]]
    hw := by decide
    g := ![![![-104, -93558, 1509], ![-356, -309350, 0]], ![![41, -5023, 81], ![133, -16606, 0]]]
    h := ![![![-337279, -168820, -94], ![10286583, 5738, 0]], ![![89358, 44725, 24], ![-2725306, -1465, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {205} * I61N1 =  Ideal.span {B.equivFun.symm ![-853, 39, 4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 5 ![![61, 0, 0], ![-4, 1, 0]]
  ![-162, 6, 1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![305, 0, 0], ![-20, 5, 0]]
    hsu := by decide
    w := ![![-810, 30, 5], ![-1315, 80, 5]]
    hw := by decide
    g := ![![![3533, 47146, -24386], ![8019, 121920, 0]], ![![-134, -2357, 1219], ![-416, -6096, 0]]]
    h := ![![![-3178, 798, -1], ![-48424, 62, 0]], ![![-5163, 1298, -2], ![-78670, 123, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {5} * I61N2 =  Ideal.span {B.equivFun.symm ![-162, 6, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS2 


noncomputable def E67RS0 : RelationCertificate Table 25 ![![67, 0, 0], ![31, 1, 0]]
  ![369, -22, -2] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![1675, 0, 0], ![775, 25, 0]]
    hsu := by decide
    w := ![![9225, -550, -50], ![-1150, 125, 0]]
    hw := by decide
    g := ![![![143, 5002, -418], ![148, 10440, 0]], ![![81, 2368, -198], ![79, 4944, 0]]]
    h := ![![![1878, 61, 0], ![-4047, -2, 0]], ![![-282, -40, -1], ![608, 67, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {25} * I67N0 =  Ideal.span {B.equivFun.symm ![369, -22, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 25 ![![67, 0, 0], ![-27, 1, 0]]
  ![-222, 11, 1] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![1675, 0, 0], ![-675, 25, 0]]
    hsu := by decide
    w := ![![-5550, 275, 25], ![1025, -100, 0]]
    hw := by decide
    g := ![![![-495700, -31767873, 2650765], ![-1032760, -66269129, 0]], ![![196348, 12582726, -1049924], ![409071, 26248101, 0]]]
    h := ![![![-690, 53, -1], ![-1704, 68, 0]], ![![188, -7, 0], ![465, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {25} * I67N1 =  Ideal.span {B.equivFun.symm ![-222, 11, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 25 ![![67, 0, 0], ![-5, 1, 0]]
  ![-147, 11, 1] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![1675, 0, 0], ![-125, 25, 0]]
    hsu := by decide
    w := ![![-3675, 275, 25], ![125, -25, 0]]
    hw := by decide
    g := ![![![-61, -4399, 367], ![-141, -9176, 0]], ![![12, 287, -24], ![24, 600, 0]]]
    h := ![![![-316, 68, -1], ![-4205, 68, 0]], ![![20, -4, 0], ![267, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {25} * I67N2 =  Ideal.span {B.equivFun.symm ![-147, 11, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E67RS2 


noncomputable def E71RS0 : RelationCertificate Table 5125 ![![71, 0, 0], ![6, 1, 0]]
  ![-33402, 1401, 191] ![![5125, 0, 0], ![-62, 1, 0]] where
    su := ![![363875, 0, 0], ![30750, 5125, 0]]
    hsu := by decide
    w := ![![-171185250, 7180125, 978875], ![1757875, -71750, -10250]]
    hw := by decide
    g := ![![![-1225226, -519143537400, 8373283180], ![-101279099, -42913076297628, 0]], ![![-103316, -43791807892, 706319509], ![-8540310, -3619887483654, 0]]]
    h := ![![![-33378, -5511, -5], ![389406, 546, 0]], ![![341, 56, 0], ![-3978, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {5125} * I71N0 =  Ideal.span {B.equivFun.symm ![-33402, 1401, 191]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 125 ![![71, 0, 0], ![22, 1, 0]]
  ![1179, -52, -7] ![![125, 0, 0], ![-62, 1, 0]] where
    su := ![![8875, 0, 0], ![2750, 125, 0]]
    hsu := by decide
    w := ![![147375, -6500, -875], ![-61625, 2625, 375]]
    hw := by decide
    g := ![![![69, 4024, -65], ![115, 8116, 0]], ![![51, 1361, -22], ![92, 2746, 0]]]
    h := ![![![2149781, 110566, 584], ![-6937876, -41471, 0]], ![![-898979, -46253, -245], ![2901228, 17398, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {125} * I71N1 =  Ideal.span {B.equivFun.symm ![1179, -52, -7]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 41 ![![71, 0, 0], ![-29, 1, 0]]
  ![2430, -136, -15] ![![41, 0, 0], ![20, 1, 0]] where
    su := ![![2911, 0, 0], ![-1189, 41, 0]]
    hsu := by decide
    w := ![![99630, -5576, -615], ![73185, -4100, -451]]
    hw := by decide
    g := ![![![-841121, 87516424, 4377924], ![1724257, -179494880, 0]], ![![324923, -33807874, -1691206], ![-666080, 69339445, 0]]]
    h := ![![![3491024, -134510, 487], ![8546906, -34592, 0]], ![![2564382, -98785, 357], ![6278253, -25358, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {41} * I71N2 =  Ideal.span {B.equivFun.symm ![2430, -136, -15]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E71RS2 


noncomputable def E73RS0 : RelationCertificate Table 3125 ![![73, 0, 0], ![-33, 1, 0]]
  ![8322, -361, -51] ![![3125, 0, 0], ![-437, 1, 0]] where
    su := ![![228125, 0, 0], ![-103125, 3125, 0]]
    hsu := by decide
    w := ![![26006250, -1128125, -159375], ![-3553125, 153125, 21875]]
    hw := by decide
    g := ![![![993310619, 22631549874424, -51788448850], ![7103193775, 161838902656222, 0]], ![![-437454794, -9966961760280, 22807695106], ![-3128252242, -71274047206241, 0]]]
    h := ![![![167160, -5651, 17], ![369526, -1292, 0]], ![![-22824, 794, -3], ![-50455, 226, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {3125} * I73N0 =  Ideal.span {B.equivFun.symm ![8322, -361, -51]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E73RS0 


noncomputable def E73RS1 : RelationCertificate Table 1025 ![![73, 0, 0], ![-28, 1, 0]]
  ![25801, -1438, -158] ![![1025, 0, 0], ![-62, 1, 0]] where
    su := ![![74825, 0, 0], ![-28700, 1025, 0]]
    hsu := by decide
    w := ![![26446025, -1473950, -161950], ![-1340700, 74825, 8200]]
    hw := by decide
    g := ![![![59, 805877, -12998], ![1061, 13322980, 0]], ![![30, -294377, 4748], ![474, -4866708, 0]]]
    h := ![![![828893697, -32993934, 121090], ![2161043360, -8839728, 0]], ![![-42021324, 1672657, -6139], ![-109555548, 448155, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {1025} * I73N1 =  Ideal.span {B.equivFun.symm ![25801, -1438, -158]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E73RS1 


noncomputable def E73RS2 : RelationCertificate Table 128125 ![![73, 0, 0], ![-13, 1, 0]]
  ![112721, -3898, -568] ![![128125, 0, 0], ![-41062, 1, 0]] where
    su := ![![9353125, 0, 0], ![-1665625, 128125, 0]]
    hsu := by decide
    w := ![![14442378125, -499431250, -72775000], ![-4627618750, 160028125, 23318750]]
    hw := by decide
    g := ![![![13639101800082316740943, 6012771711297897079486348629, -146431535522625683361460], ![42557837371183742448817, 18761540488836415680687062504, 0]], ![![-2522299647962996645101, -1111950932912387147656811871, 27079804514485747460882], ![-7870284993309116583546, -3469599953418486393425506248, 0]]]
    h := ![![![212636891600, -16800538156, 34142627], ![1194037921083, -2492412339, 0]], ![![-68132994326, 5383219081, -10939962], ![-382592965360, 798617408, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {128125} * I73N2 =  Ideal.span {B.equivFun.symm ![112721, -3898, -568]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E73RS2 
