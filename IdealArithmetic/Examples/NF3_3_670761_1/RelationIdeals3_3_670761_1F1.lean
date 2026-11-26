import IdealArithmetic.Examples.NF3_3_670761_1.PrimesBelow3_3_670761_1F1
import IdealArithmetic.Examples.NF3_3_670761_1.ClassGroupData3_3_670761_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 289 ![![37, 0, 0], ![15, 1, 0]]
  ![54, 12, 13] ![![289, 0, 0], ![96, 1, 0]] where
    su := ![![10693, 0, 0], ![4335, 289, 0]]
    hsu := by decide
    w := ![![15606, 3468, 3757], ![5202, 1445, 1445]]
    hw := by decide
    g := ![![![-16995, 336095, 40625], ![-4426, -1067330, 0]], ![![-7076, 139592, 16873], ![-1786, -443300, 0]]]
    h := ![![![-558, 1260, 1381], ![-168, -4644, 0]], ![![-186, 415, 455], ![-50, -1530, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {289} * I37N0 =  Ideal.span {B.equivFun.symm ![54, 12, 13]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 289 ![![37, 0, 0], ![-13, 1, 0]]
  ![203, 13, -10] ![![289, 0, 0], ![96, 1, 0]] where
    su := ![![10693, 0, 0], ![-3757, 289, 0]]
    hsu := by decide
    w := ![![58667, 3757, -2890], ![19363, 1156, -867]]
    hw := by decide
    g := ![![![7533, -151010, -18253], ![2300, 479556, 0]], ![![-2553, 49754, 6014], ![-544, -158004, 0]]]
    h := ![![![6854, 26806, -16354], ![-1665, 55008, 0]], ![![2270, 8849, -5399], ![-529, 18160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {289} * I37N1 =  Ideal.span {B.equivFun.symm ![203, 13, -10]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E37RS1 


noncomputable def E37RS2 : RelationCertificate Table 289 ![![37, 0, 0], ![-2, 1, 0]]
  ![-438, -1, 23] ![![289, 0, 0], ![96, 1, 0]] where
    su := ![![10693, 0, 0], ![-578, 289, 0]]
    hsu := by decide
    w := ![![-126582, -289, 6647], ![-41905, 0, 2312]]
    hw := by decide
    g := ![![![-311757886, 6171266274, 745942858], ![-82205597, -19597953270, 0]], ![![13714920, -271489009, -32815840], ![3616627, 862161615, 0]]]
    h := ![![![-4268, -5968, 9375], ![91, -31532, 0]], ![![-1413, -1976, 3104], ![32, -10440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {289} * I37N2 =  Ideal.span {B.equivFun.symm ![-438, -1, 23]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E37RS2 


noncomputable def E41RS0 : RelationCertificate Table 2057 ![![41, 0, 0], ![19, 1, 0]]
  ![-82, 165, -72] ![![2057, 0, 0], ![15119, 1423, -830]] where
    su := ![![84337, 0, 0], ![39083, 2057, 0]]
    hsu := by decide
    w := ![![-168674, 339405, -148104], ![-4148969, -3645004, 2038487]]
    hw := by decide
    g := ![![![1052251393740, -8150353309781, 8930841255511], ![-1507808522522, -1705835133120, 0]], ![![637792960717, -4940110417773, 5413181520355], ![-913916279606, -1033944614400, 0]]]
    h := ![![![-1796, 5905, 4622], ![-664, -17234, 0]], ![![-35501, 117166, 91857], ![-13574, -342286, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {2057} * I41N0 =  Ideal.span {B.equivFun.symm ![-82, 165, -72]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 2057 ![![41, 0, 0], ![-11, 1, 0]]
  ![3782, 66, -141] ![![2057, 0, 0], ![15119, 1423, -830]] where
    su := ![![84337, 0, 0], ![-22627, 2057, 0]]
    hsu := by decide
    w := ![![7779574, 135762, -290037], ![54592780, 1322651, -2238016]]
    hw := by decide
    g := ![![![-369513104864, 2862112903701, -3136192386990], ![529488486510, 599028356415, 0]], ![![45266148218, -350615048197, 384190379826], ![-64863488337, -73382274765, 0]]]
    h := ![![![962468274, 3238157262, -2223227509], ![-179243708, 8286575248, 0]], ![![6752312434, 22717683665, -15597321304], ![-1257506166, 58135470216, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2057} * I41N1 =  Ideal.span {B.equivFun.symm ![3782, 66, -141]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 2057 ![![41, 0, 0], ![-8, 1, 0]]
  ![-250, -99, -69] ![![2057, 0, 0], ![15119, 1423, -830]] where
    su := ![![84337, 0, 0], ![-16456, 2057, 0]]
    hsu := by decide
    w := ![![-514250, -203643, -141933], ![-3457817, -886567, -861883]]
    hw := by decide
    g := ![![![-39947231, 309325632, -338947598], ![57226763, 64740800, 0]], ![![7182505, -55742505, 61079803], ![-10310174, -11666400, 0]]]
    h := ![![![11542806, 30809289, -26038429], ![-1500788, 97052320, 0]], ![![79967255, 213443337, -180391339], ![-10397408, 672367680, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {2057} * I41N2 =  Ideal.span {B.equivFun.symm ![-250, -99, -69]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E41RS2 


noncomputable def E43RS0 : RelationCertificate Table 3179 ![![43, 0, 0], ![19, 1, 0]]
  ![-1425, 165, -38] ![![3179, 0, 0], ![10595, 333, -637]] where
    su := ![![136697, 0, 0], ![60401, 3179, 0]]
    hsu := by decide
    w := ![![-4530075, 524535, -120802], ![-16200184, -1443266, 1198483]]
    hw := by decide
    g := ![![![-4089865850501, -80080265363170, 2380037326573], ![-22496049303336, -45807786751884, 0]], ![![-1880309344254, -36816775132733, 1094218390228], ![-10342523027952, -21060057387741, 0]]]
    h := ![![![-665073040, 2169035375, 1699794079], ![-243426770, -6644649585, 0]], ![![-2364111290, 7710192370, 6042197169], ![-865300504, -23619497990, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {3179} * I43N0 =  Ideal.span {B.equivFun.symm ![-1425, 165, -38]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 3179 ![![43, 0, 0], ![-11, 1, 0]]
  ![2031, 66, -73] ![![3179, 0, 0], ![10595, 333, -637]] where
    su := ![![136697, 0, 0], ![-34969, 3179, 0]]
    hsu := by decide
    w := ![![6456549, 209814, -232067], ![20777944, 251141, -855151]]
    hw := by decide
    g := ![![![1792877, 35230021, -1046680], ![9898752, 20152512, 0]], ![![-447272, -8728801, 259513], ![-2451628, -4993052, 0]]]
    h := ![![![52864, 176911, -121477], ![-9379, 474858, 0]], ![![170198, 569617, -391133], ![-30252, 1528950, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {3179} * I43N1 =  Ideal.span {B.equivFun.symm ![2031, 66, -73]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 3179 ![![43, 0, 0], ![-8, 1, 0]]
  ![479, -22, -72] ![![3179, 0, 0], ![10595, 333, -637]] where
    su := ![![136697, 0, 0], ![-25432, 3179, 0]]
    hsu := by decide
    w := ![![1522741, -69938, -228888], ![4822543, 238425, 85833]]
    hw := by decide
    g := ![![![-967914837471, -18951936143682, 563263811174], ![-5323954506934, -10840951206358, 0]], ![![99247441738, 1943281863489, -57755594478], ![545904345064, 1111602725212, 0]]]
    h := ![![![119403701, 317963063, -268754040], ![-14820147, 1050583968, 0]], ![![375905719, 1001008621, -846089183], ![-46656660, 3307439536, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {3179} * I43N2 =  Ideal.span {B.equivFun.symm ![479, -22, -72]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E43RS2 


noncomputable def E47RS0 : RelationCertificate Table 187 ![![47, 0, 0], ![12, 1, 0]]
  ![279, 11, -15] ![![187, 0, 0], ![317, 5, -20]] where
    su := ![![8789, 0, 0], ![2244, 187, 0]]
    hsu := by decide
    w := ![![52173, 2057, -2805], ![84898, 1122, -2805]]
    hw := by decide
    g := ![![![1212731841, 5320425949, 1655735999], ![2020981251, 5982289040, 0]], ![![340497656, 1493811899, 464879731], ![567429428, 1679642692, 0]]]
    h := ![![![-784, 1155, 1810], ![-129, -7735, 0]], ![![-1268, 1893, 2965], ![-275, -12670, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {187} * I47N0 =  Ideal.span {B.equivFun.symm ![279, 11, -15]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 187 ![![47, 0, 0], ![14, 1, 0]]
  ![-20, 22, -13] ![![187, 0, 0], ![317, 5, -20]] where
    su := ![![8789, 0, 0], ![2618, 187, 0]]
    hsu := by decide
    w := ![![-3740, 4114, -2431], ![-11220, -2431, 2244]]
    hw := by decide
    g := ![![![-23030, -99690, -31003], ![-37685, -112086, 0]], ![![-7345, -32211, -10024], ![-12234, -36218, 0]]]
    h := ![![![-661298, 1284888, 1566007], ![-169616, -6691122, 0]], ![![-1915323, 3721453, 4535667], ![-491301, -19379667, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {187} * I47N1 =  Ideal.span {B.equivFun.symm ![-20, 22, -13]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 187 ![![47, 0, 0], ![21, 1, 0]]
  ![-75, -11, -2] ![![187, 0, 0], ![317, 5, -20]] where
    su := ![![8789, 0, 0], ![3927, 187, 0]]
    hsu := by decide
    w := ![![-14025, -2057, -374], ![-22440, 1683, 2431]]
    hw := by decide
    g := ![![![-2678704737, -11751853084, -3657219579], ![-4463979524, -13213788240, 0]], ![![-1216078554, -5335107431, -1660304914], ![-2026557921, -5998796900, 0]]]
    h := ![![![-628, 2264, 1554], ![-179, -6640, 0]], ![![-1002, 3715, 2549], ![-356, -10890, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {187} * I47N2 =  Ideal.span {B.equivFun.symm ![-75, -11, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E47RS2 


noncomputable def E79RS0 : RelationCertificate Table 187 ![![79, 0, 0], ![27, 1, 0]]
  ![54, -22, -21] ![![187, 0, 0], ![317, 5, -20]] where
    su := ![![14773, 0, 0], ![5049, 187, 0]]
    hsu := by decide
    w := ![![10098, -4114, -3927], ![17578, 6171, 4488]]
    hw := by decide
    g := ![![![-118163078, -518397770, -161327275], ![-196915045, -582886656, 0]], ![![-1150269412, -5046393452, -1570456069], ![-1916888972, -5674166788, 0]]]
    h := ![![![1018, -4986, -2491], ![336, 17888, 0]], ![![1752, -8519, -4256], ![538, 30568, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {187} * I79N0 =  Ideal.span {B.equivFun.symm ![54, -22, -21]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 187 ![![79, 0, 0], ![-20, 1, 0]]
  ![-25, -66, -63] ![![187, 0, 0], ![317, 5, -20]] where
    su := ![![14773, 0, 0], ![-3740, 187, 0]]
    hsu := by decide
    w := ![![-4675, -12342, -11781], ![-6545, 17578, 17204]]
    hw := by decide
    g := ![![![-8986, -39078, -12156], ![-14799, -43938, 0]], ![![1762, 8083, 2521], ![3119, 9090, 0]]]
    h := ![![![-1614245, -8456887, 3719349], ![301657, -26711694, 0]], ![![-2426275, -12711040, 5590334], ![453404, -40148754, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {187} * I79N1 =  Ideal.span {B.equivFun.symm ![-25, -66, -63]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 187 ![![79, 0, 0], ![-7, 1, 0]]
  ![857, 11, -32] ![![187, 0, 0], ![317, 5, -20]] where
    su := ![![14773, 0, 0], ![-1309, 187, 0]]
    hsu := by decide
    w := ![![160259, 2057, -5984], ![265914, 5797, -10659]]
    hw := by decide
    g := ![![![1631902332, 7159385013, 2228026763], ![2719515733, 8050015334, 0]], ![![-126004927, -552800835, -172033631], ![-209983131, -621569475, 0]]]
    h := ![![![35807660, 86406798, -79182108], ![-2079031, 568671500, 0]], ![![59402970, 143344203, -131358833], ![-3449006, 943395250, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {187} * I79N2 =  Ideal.span {B.equivFun.symm ![857, 11, -32]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS2 
