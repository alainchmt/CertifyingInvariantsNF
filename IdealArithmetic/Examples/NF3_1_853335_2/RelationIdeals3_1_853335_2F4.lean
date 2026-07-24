import IdealArithmetic.Examples.NF3_1_853335_2.PrimesBelow3_1_853335_2F4
import IdealArithmetic.Examples.NF3_1_853335_2.ClassGroupData3_1_853335_2

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 325 ![![199, 0, 0], ![36, 1, 0]]
  ![151, 6, -17] ![![325, 0, 0], ![-74, 1, 0]] where
    su := ![![64675, 0, 0], ![11700, 325, 0]]
    hsu := by decide
    w := ![![49075, 1950, -5525], ![-14625, -650, 1300]]
    hw := by decide
    g := ![![![-172, -328568, 31081], ![-753, -1443045, 0]], ![![12, -61917, 5857], ![53, -271932, 0]]]
    h := ![![![2113, 54, -1], ![-11676, 26, 0]], ![![-675, -24, -1], ![3730, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {325} * I199N1 =  Ideal.span {B.equivFun.symm ![151, 6, -17]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E199RS1 


noncomputable def E211RS1 : RelationCertificate Table 13 ![![211, 0, 0], ![16, 1, 0]]
  ![200, 7, -9] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![2743, 0, 0], ![208, 13, 0]]
    hsu := by decide
    w := ![![2600, 91, -117], ![-1027, 39, 13]]
    hw := by decide
    g := ![![![19, 485, 848], ![48, -1570, 0]], ![![2, 37, 65], ![10, -120, 0]]]
    h := ![![![952, 55, -2], ![-12542, 59, 0]], ![![-405, -39, -6], ![5336, 181, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {13} * I211N1 =  Ideal.span {B.equivFun.symm ![200, 7, -9]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E211RS1 


noncomputable def E223RS0 : RelationCertificate Table 169 ![![223, 0, 0], ![40, 1, 0]]
  ![653, 90, -60] ![![169, 0, 0], ![-74, 1, 0]] where
    su := ![![37687, 0, 0], ![6760, 169, 0]]
    hsu := by decide
    w := ![![110357, 15210, -10140], ![-60502, -7267, 5070]]
    hw := by decide
    g := ![![![-197, -92866, 8784], ![-428, -212088, 0]], ![![-12, -17445, 1650], ![-22, -39840, 0]]]
    h := ![![![3146051, 82076, 599], ![-17539218, -19091, 0]], ![![-1724746, -45011, -331], ![9615450, 10549, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N0 : Ideal.span {169} * I223N0 =  Ideal.span {B.equivFun.symm ![653, 90, -60]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E223RS0 


noncomputable def E223RS1 : RelationCertificate Table 169 ![![223, 0, 0], ![89, 1, 0]]
  ![1207, 200, 92] ![![169, 0, 0], ![-74, 1, 0]] where
    su := ![![37687, 0, 0], ![15041, 169, 0]]
    hsu := by decide
    w := ![![203983, 33800, 15548], ![-70642, -11661, -5408]]
    hw := by decide
    g := ![![![127, 38729, -3664], ![271, 88452, 0]], ![![95, 15527, -1469], ![210, 35463, 0]]]
    h := ![![![5943431, 94709, 2197], ![-14891954, -69977, 0]], ![![-2058338, -32865, -766], ![5157404, 24398, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {169} * I223N1 =  Ideal.span {B.equivFun.symm ![1207, 200, 92]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E223RS1 


noncomputable def E223RS2 : RelationCertificate Table 169 ![![223, 0, 0], ![94, 1, 0]]
  ![-337, -48, 32] ![![169, 0, 0], ![-74, 1, 0]] where
    su := ![![37687, 0, 0], ![15886, 169, 0]]
    hsu := by decide
    w := ![![-56953, -8112, 5408], ![31434, 3887, -2704]]
    hw := by decide
    g := ![![![609, 269534, -25497], ![1384, 615575, 0]], ![![304, 115342, -10911], ![691, 263425, 0]]]
    h := ![![![-3267925, -43375, -641], ![7752627, 20425, 0]], ![![1803210, 23817, 345], ![-4277826, -10993, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N2 : Ideal.span {169} * I223N2 =  Ideal.span {B.equivFun.symm ![-337, -48, 32]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E223RS2 


noncomputable def E227RS0 : RelationCertificate Table 25 ![![227, 0, 0], ![2, 1, 0]]
  ![-227, -37, -16] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![5675, 0, 0], ![50, 25, 0]]
    hsu := by decide
    w := ![![-5675, -925, -400], ![-3475, -600, -275]]
    hw := by decide
    g := ![![![2535966947, -1587515304477, -11130358899930], ![-63399173497, 39751281785461, 0]], ![![11171702, -6993486447, -49032607048], ![-279292569, 175116453743, 0]]]
    h := ![![![-11029, -5515, -3], ![1251678, 95, 0]], ![![-6753, -3378, -6], ![766396, 193, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N0 : Ideal.span {25} * I227N0 =  Ideal.span {B.equivFun.symm ![-227, -37, -16]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E227RS0 


noncomputable def E227RS1 : RelationCertificate Table 25 ![![227, 0, 0], ![11, 1, 0]]
  ![468, -17, -6] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![5675, 0, 0], ![275, 25, 0]]
    hsu := by decide
    w := ![![11700, -425, -150], ![-750, 325, -125]]
    hw := by decide
    g := ![![![9254, -5739309, -40239433], ![-229199, 143712284, 0]], ![![634, -390930, -2740889], ![-15600, 9788892, 0]]]
    h := ![![![1368, 121, -2], ![-28188, 64, 0]], ![![-108, -16, -4], ![2226, 129, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {25} * I227N1 =  Ideal.span {B.equivFun.symm ![468, -17, -6]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E227RS1 


noncomputable def E227RS2 : RelationCertificate Table 25 ![![227, 0, 0], ![-13, 1, 0]]
  ![-47, -7, -1] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![5675, 0, 0], ![-325, 25, 0]]
    hsu := by decide
    w := ![![-1175, -175, -25], ![-250, -75, -50]]
    hw := by decide
    g := ![![![6, -115, -806], ![10, 2877, 0]], ![![-1, 5, 37], ![6, -132, 0]]]
    h := ![![![-88, 16, -5], ![-1533, 162, 0]], ![![-6, 6, -3], ![-104, 97, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N2 : Ideal.span {25} * I227N2 =  Ideal.span {B.equivFun.symm ![-47, -7, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E227RS2 


noncomputable def E229RS0 : RelationCertificate Table 5 ![![229, 0, 0], ![-97, 1, 0]]
  ![31, 6, 3] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![1145, 0, 0], ![-485, 5, 0]]
    hsu := by decide
    w := ![![155, 30, 15], ![640, 100, 45]]
    hw := by decide
    g := ![![![-7, 53, 367], ![13, -263, 0]], ![![1, -23, -152], ![-1, 109, 0]]]
    h := ![![![1794, 51, -5], ![4235, 164, 0]], ![![6838, -56, -1], ![16142, 34, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N0 : Ideal.span {5} * I229N0 =  Ideal.span {B.equivFun.symm ![31, 6, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E229RS0 


noncomputable def E229RS1 : RelationCertificate Table 5 ![![229, 0, 0], ![-85, 1, 0]]
  ![-619, -104, -47] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![1145, 0, 0], ![-425, 5, 0]]
    hsu := by decide
    w := ![![-3095, -520, -235], ![-10160, -1710, -775]]
    hw := by decide
    g := ![![![153, -1007, -7383], ![-169, 5267, 0]], ![![-65, 378, 2773], ![63, -1978, 0]]]
    h := ![![![-30586, 454, -8], ![-82395, 255, 0]], ![![-100588, 1295, -10], ![-270972, 305, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {5} * I229N1 =  Ideal.span {B.equivFun.symm ![-619, -104, -47]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E229RS1 


noncomputable def E229RS2 : RelationCertificate Table 5 ![![229, 0, 0], ![-47, 1, 0]]
  ![39, 4, -3] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![1145, 0, 0], ![-235, 5, 0]]
    hsu := by decide
    w := ![![195, 20, -15], ![-570, -20, 25]]
    hw := by decide
    g := ![![![-27, 41, 319], ![3, -229, 0]], ![![4, -9, -67], ![0, 48, 0]]]
    h := ![![![440, 4, -2], ![2143, 65, 0]], ![![-1156, 65, -6], ![-5630, 197, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N2 : Ideal.span {5} * I229N2 =  Ideal.span {B.equivFun.symm ![39, 4, -3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E229RS2 


noncomputable def E239RS0 : RelationCertificate Table 13 ![![239, 0, 0], ![62, 1, 0]]
  ![-81, -12, -5] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![3107, 0, 0], ![806, 13, 0]]
    hsu := by decide
    w := ![![-1053, -156, -65], ![-1339, -234, -104]]
    hw := by decide
    g := ![![![32, -1849, -3256], ![-128, 6046, 0]], ![![6, -485, -853], ![-27, 1584, 0]]]
    h := ![![![-549, -53, -5], ![2115, 170, 0]], ![![-767, -21, -1], ![2955, 33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N0 : Ideal.span {13} * I239N0 =  Ideal.span {B.equivFun.symm ![-81, -12, -5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E239RS0 


noncomputable def E239RS1 : RelationCertificate Table 13 ![![239, 0, 0], ![80, 1, 0]]
  ![-44, -7, -4] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![3107, 0, 0], ![1040, 13, 0]]
    hsu := by decide
    w := ![![-572, -91, -52], ![-988, -156, -65]]
    hw := by decide
    g := ![![![55, -3562, -6264], ![-246, 11635, 0]], ![![17, -1193, -2097], ![-75, 3895, 0]]]
    h := ![![![-116, -47, -4], ![346, 136, 0]], ![![-84, -58, -5], ![250, 170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {13} * I239N1 =  Ideal.span {B.equivFun.symm ![-44, -7, -4]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E239RS1 


noncomputable def E239RS2 : RelationCertificate Table 13 ![![239, 0, 0], ![97, 1, 0]]
  ![-43, -3, 2] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![3107, 0, 0], ![1261, 13, 0]]
    hsu := by decide
    w := ![![-559, -39, 26], ![234, -13, -13]]
    hw := by decide
    g := ![![![291048, -13460995, -23684075], ![-945904, 43984710, 0]], ![![119195, -5512952, -9699814], ![-387384, 18013940, 0]]]
    h := ![![![-1124, -81, -5], ![2769, 171, 0]], ![![272, -11, -1], ![-670, 34, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N2 : Ideal.span {13} * I239N2 =  Ideal.span {B.equivFun.symm ![-43, -3, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E239RS2 


noncomputable def E241RS1 : RelationCertificate Table 25 ![![241, 0, 0], ![-89, 1, 0]]
  ![-9, -4, 3] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![6025, 0, 0], ![-2225, 25, 0]]
    hsu := by decide
    w := ![![-225, -100, 75], ![600, 50, -25]]
    hw := by decide
    g := ![![![2973, -1858707, -13031729], ![-74205, 46541889, 0]], ![![-886, 553401, 3879997], ![22104, -13857132, 0]]]
    h := ![![![-318, 80, -6], ![-861, 207, 0]], ![![1026, 52, -5], ![2778, 172, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {25} * I241N1 =  Ideal.span {B.equivFun.symm ![-9, -4, 3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E241RS1 
