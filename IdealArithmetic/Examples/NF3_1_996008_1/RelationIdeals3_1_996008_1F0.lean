import IdealArithmetic.Examples.NF3_1_996008_1.PrimesBelow3_1_996008_1F0
import IdealArithmetic.Examples.NF3_1_996008_1.ClassGroupData3_1_996008_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 81 ![![2, 0, 0], ![0, 1, 0]]
  ![3840228, -155197, -51892] ![![81, 0, 0], ![14, 1, 0]] where
    su := ![![162, 0, 0], ![0, 81, 0]]
    hsu := by decide
    w := ![![311058468, -12570957, -4203252], ![43488576, 370170, -881685]]
    hw := by decide
    g := ![![![-631544971, -170802184, -23788790], ![-111264514, 426205, 0]], ![![-2284990391, -617791450, -86056744], ![-402563646, 458990, 0]]]
    h := ![![![1920114, -62079, 0], ![-31039, -51892, 0]], ![![268448, 3656, -4354], ![-2742, -2177, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {81} * I2N0 =  Ideal.span {B.equivFun.symm ![3840228, -155197, -51892]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 729 ![![2, 0, 0], ![1, 1, 0]]
  ![-117, -25, -4] ![![729, 0, 0], ![-48, -1, 1]] where
    su := ![![1458, 0, 0], ![729, 729, 0]]
    hsu := by decide
    w := ![![-85293, -18225, -2916], ![1458, 0, 0]]
    hw := by decide
    g := ![![![23278342, -2717837, -115979], ![-1528469, -86077161, 0]], ![![33528431, -3914581, -167047], ![-2202187, -123979450, 0]]]
    h := ![![![-78, -40, -10], ![39, 16, 0]], ![![0, -1, 0], ![2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {729} * I2N1 =  Ideal.span {B.equivFun.symm ![-117, -25, -4]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 2187 ![![3, 0, 0], ![1, 1, 0]]
  ![23058056061, 6097861477, 842689393] ![![2187, 0, 0], ![681, -1, 1]] where
    su := ![![6561, 0, 0], ![2187, 2187, 0]]
    hsu := by decide
    w := ![![50427968605407, 13336023050199, 1842961702491], ![16743060250173, 4427817411690, 611898906042]]
    hw := by decide
    g := ![![![17956, 70930, -98], ![6585, -219880, 0]], ![![17766, 69734, -118], ![6977, -215817, 0]]]
    h := ![![![6288560743, 6288560743, 5934294659], ![4192373832, -16960194584, 0]], ![![2087923712, 2087923712, 1970300525], ![1391949143, -5631112409, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {2187} * I3N1 =  Ideal.span {B.equivFun.symm ![23058056061, 6097861477, 842689393]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 1 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![3, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![2, 1, -2], ![3, 6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![2, 1, -2], ![3, 6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {1} * I3N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS2 


noncomputable def E5RS0 : RelationCertificate Table 2187 ![![5, 0, 0], ![-16, -3, 1]]
  ![-6651, -1768, -244] ![![2187, 0, 0], ![681, -1, 1]] where
    su := ![![10935, 0, 0], ![-34992, -6561, 2187]]
    hsu := by decide
    w := ![![-14545737, -3866616, -533628], ![-4831083, -1283769, -177147]]
    hw := by decide
    g := ![![![-8567, -31496, 45], ![-854, 97565, 0]], ![![21678, 85799, -125], ![7654, -265772, 0]]]
    h := ![![![-95, -122, -126], ![386, 0, 0]], ![![-29, -40, -42], ![129, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2187} * I5N0 =  Ideal.span {B.equivFun.symm ![-6651, -1768, -244]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 3 ![![5, 0, 0], ![-2, 1, 0]]
  ![3578107, 946255, 130767] ![![3, 0, 0], ![-18, -1, 1]] where
    su := ![![15, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![10734321, 2838765, 392301], ![97060698, 25668369, 3547221]]
    hw := by decide
    g := ![![![-43, 642, -86], ![-11, 0, 0]], ![![-68, -508, -29], ![582, 0, 0]]]
    h := ![![![23461753, -12447714, 658103], ![56865329, -3159748, 0]], ![![212143266, -112553351, 5950631], ![514181382, -28570748, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {3} * I5N1 =  Ideal.span {B.equivFun.symm ![3578107, 946255, 130767]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E5RS1 


noncomputable def E11RS0 : RelationCertificate Table 81 ![![11, 0, 0], ![0, 1, 0]]
  ![-99, 28, -2] ![![81, 0, 0], ![14, 1, 0]] where
    su := ![![891, 0, 0], ![0, 81, 0]]
    hsu := by decide
    w := ![![-8019, 2268, -162], ![-1782, 243, 0]]
    hw := by decide
    g := ![![![-9, -392, -28], ![40, 2262, 0]], ![![-6, -126, -9], ![27, 725, 0]]]
    h := ![![![-9, 2, 0], ![6, -2, 0]], ![![-2, 0, 0], ![3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {81} * I11N0 =  Ideal.span {B.equivFun.symm ![-99, 28, -2]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![5, 1, 0]]
  ![185368555, 49021989, 6774557] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![33, 0, 0], ![15, 3, 0]]
    hsu := by decide
    w := ![![556105665, 147065967, 20323671], ![1341362286, 354732480, 49021989]]
    hw := by decide
    g := ![![![-28831, 140, 529], ![49, 0, 0]], ![![-3583, -1213, 255], ![-404, -1, 0]]]
    h := ![![![1070628190, 303276906, 18228881], ![-2318308307, -193743134, 0]], ![![2582423402, 731523222, 43969223], ![-5591907332, -467320790, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![185368555, 49021989, 6774557]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 81 ![![11, 0, 0], ![-5, 1, 0]]
  ![765, 202, 28] ![![81, 0, 0], ![-48, -1, 1]] where
    su := ![![891, 0, 0], ![-405, 81, 0]]
    hsu := by decide
    w := ![![61965, 16362, 2268], ![-2268, -567, -81]]
    hw := by decide
    g := ![![![-3517, 580, -2], ![2104, 1950, 0]], ![![1469, -235, 0], ![-787, -793, 0]]]
    h := ![![![345690, -79623, 2106], ![760365, -23138, 0]], ![![-12658, 2920, -78], ![-27842, 857, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {81} * I11N2 =  Ideal.span {B.equivFun.symm ![765, 202, 28]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 2187 ![![13, 0, 0], ![2, 1, 0]]
  ![970516629, 256659796, 35468908] ![![2187, 0, 0], ![662, 1, 0]] where
    su := ![![28431, 0, 0], ![4374, 2187, 0]]
    hsu := by decide
    w := ![![2122519867623, 561314973852, 77570501796], ![649504852182, 171766024281, 23737076892]]
    hw := by decide
    g := ![![![-635, 1581138, 2386], ![2218, -5223450, 0]], ![![-582, 421307, 637], ![1820, -1391843, 0]]]
    h := ![![![3587051100395, 1842290743387, 24394117223], ![-23315346894253, -317088054991, 0]], ![![1097660912514, 563752921801, 7464758159], ![-7134647439148, -97031002351, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {2187} * I13N0 =  Ideal.span {B.equivFun.symm ![970516629, 256659796, 35468908]} * (J0 ^ 7*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_0 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 9 ![![13, 0, 0], ![-4, 1, 0]]
  ![-43281, -734, 928] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![117, 0, 0], ![-36, 9, 0]]
    hsu := by decide
    w := ![![-389529, -6606, 8352], ![356868, -17145, -4446]]
    hw := by decide
    g := ![![![-5487969, -1921861, -246300], ![2225563, 86264, 0]], ![![-1367008, -498978, -56122], ![552125, -25248, 0]]]
    h := ![![![-1715701, 460694, -8093], ![-5565208, 106137, 0]], ![![1575732, -423213, 7436], ![5111216, -97162, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {9} * I13N1 =  Ideal.span {B.equivFun.symm ![-43281, -734, 928]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 9 ![![17, 0, 0], ![8, 1, 0]]
  ![-64995, 8555, 59] ![![9, 0, 0], ![-21, -1, 1]] where
    su := ![![153, 0, 0], ![72, 9, 0]]
    hsu := by decide
    w := ![![-584955, 76995, 531], ![3047103, 109422, -73314]]
    hw := by decide
    g := ![![![-11637921, -17460695, -6008099], ![28427686, 30, 0]], ![![-10430418, -15649092, -5384730], ![25478134, 17, 0]]]
    h := ![![![-1462299, -286274, -13055], ![3099261, 221994, 0]], ![![7799263, 1516695, 67466], ![-16531113, -1155068, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {9} * I17N1 =  Ideal.span {B.equivFun.symm ![-64995, 8555, 59]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 243 ![![19, 0, 0], ![-8, 1, 0]]
  ![540171, 20710, -13178] ![![243, 0, 0], ![-48, -1, 1]] where
    su := ![![4617, 0, 0], ![-1944, 243, 0]]
    hsu := by decide
    w := ![![131261553, 5032530, -3202254], ![-19218384, -3296295, 822555]]
    hw := by decide
    g := ![![![438283703, -54944874, -2129706], ![-86357135, -564298095, 0]], ![![-164948926, 20108474, 739197], ![32502832, 210536665, 0]]]
    h := ![![![1322672505, -185019736, 2460596], ![3141279678, -46764502, 0]], ![![-192888448, 26992831, -360198], ![-458100178, 6847147, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {243} * I19N1 =  Ideal.span {B.equivFun.symm ![540171, 20710, -13178]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 27 ![![23, 0, 0], ![-10, 1, 0]]
  ![-873, -328, 62] ![![27, 0, 0], ![-13, 1, 0]] where
    su := ![![621, 0, 0], ![-270, 27, 0]]
    hsu := by decide
    w := ![![-23571, -8856, 1674], ![23625, 4941, -1134]]
    hw := by decide
    g := ![![![2024, 1335, 40], ![-911, 1350, 0]], ![![-242, -275, 4], ![112, -400, 0]]]
    h := ![![![-4001, 429, -2], ![-9115, 108, 0]], ![![4035, -430, 2], ![9193, -88, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {27} * I23N1 =  Ideal.span {B.equivFun.symm ![-873, -328, 62]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 27 ![![29, 0, 0], ![1, 1, 0]]
  ![-2817, -745, -103] ![![27, 0, 0], ![-13, 1, 0]] where
    su := ![![783, 0, 0], ![27, 27, 0]]
    hsu := by decide
    w := ![![-76059, -20115, -2781], ![16227, 4293, 594]]
    hw := by decide
    g := ![![![-80936, -5591168, 430569], ![-168085, -11625350, 0]], ![![-5884, -406630, 31314], ![-12227, -845480, 0]]]
    h := ![![![-97, -97, -75], ![-4, 2072, 0]], ![![20, 20, 16], ![21, -442, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {27} * I29N1 =  Ideal.span {B.equivFun.symm ![-2817, -745, -103]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 2187 ![![31, 0, 0], ![-13, 1, 0]]
  ![-15929343, 4086574, -260528] ![![2187, 0, 0], ![681, -1, 1]] where
    su := ![![67797, 0, 0], ![-28431, 2187, 0]]
    hsu := by decide
    w := ![![-34837473141, 8937337338, -569774736], ![-9987156387, 2855979243, -203948685]]
    hw := by decide
    g := ![![![169797758, 49244255, 6783277], ![52854359, 122290, 0]], ![![-31569807, -9151155, -1261218], ![-9824702, -37590, 0]]]
    h := ![![![-116003207, 9917222, -77758], ![-275397698, 2149970, 0]], ![![-33271069, 2847920, -22840], ![-78987426, 614785, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {2187} * I31N1 =  Ideal.span {B.equivFun.symm ![-15929343, 4086574, -260528]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E31RS1 
