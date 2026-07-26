import IdealArithmetic.Examples.NF4_4_54381317_1.PrimesBelow4_4_54381317_1F0
import IdealArithmetic.Examples.NF4_4_54381317_1.ClassGroupData4_4_54381317_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0, 0], ![-132, -67, -4, 1]]
  ![-126, -67, -4, 1] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![27, 0, 0, 0], ![-1188, -603, -36, 9]]
    hsu := by decide
    w := ![![-1134, -603, -36, 9], ![-1107, -603, -36, 9]]
    hw := by decide
    g := ![![![127, 67, 4, -1], ![10, 0, 0, 0]], ![![25, -66, -22, 0], ![592, 198, 0, 0]]]
    h := ![![![152, -159, -54, 3], ![370, 126, 0, 0]], ![![140, -160, -53, 3], ![361, 123, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![-126, -67, -4, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0, 0], ![1, 1, 0, 0]]
  ![1, 0, 0, 0] ![![3, 0, 0, 0], ![1, 1, 0, 0]] where
    su := ![![3, 0, 0, 0], ![1, 1, 0, 0]]
    hsu := by decide
    w := ![![3, 0, 0, 0], ![1, 1, 0, 0]]
    hw := by decide
    g := ![![![0, -2, 1, 2], ![3, 3, -6, 0]], ![![0, 0, 1, 1], ![1, 0, -3, 0]]]
    h := ![![![0, -2, 1, 2], ![3, 3, -6, 0]], ![![0, 0, 1, 1], ![1, 0, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 1 ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
  ![1, 0, 0, 0] ![![3, 0, 0, 0], ![-1, 1, 0, 0]] where
    su := ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
    hsu := by decide
    w := ![![3, 0, 0, 0], ![-1, 1, 0, 0]]
    hw := by decide
    g := ![![![2, 1, 0, -2], ![3, 6, 6, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]]]
    h := ![![![2, 1, 0, -2], ![3, 6, 6, 0]], ![![0, 0, 0, 0], ![1, 0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {1} * I3N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS2 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0, 0], ![-133, -67, -4, 1]]
  ![-138, -67, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![15, 0, 0, 0], ![-399, -201, -12, 3]]
    hsu := by decide
    w := ![![-414, -201, -12, 3], ![843, 402, 24, -6]]
    hw := by decide
    g := ![![![42, 0, -4, 0], ![37, 12, 0, 0]], ![![-198, 603, 174, -9], ![-1214, -414, 0, 0]]]
    h := ![![![2619, -6322, -1789, 132], ![18256, 6305, 0, 0]], ![![-5138, 13009, 3658, -271], ![-37257, -12870, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![-138, -67, -4, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 9 ![![5, 0, 0, 0], ![2, 1, 0, 0]]
  ![-73, -50, -6, 1] ![![9, 0, 0, 0], ![-4, 1, 0, 0]] where
    su := ![![45, 0, 0, 0], ![18, 9, 0, 0]]
    hsu := by decide
    w := ![![-657, -450, -54, 9], ![675, 459, 54, -9]]
    hw := by decide
    g := ![![![-615, -14567, 3677, 0], ![-1339, -33092, 1, 0]], ![![5, 15, -4, 0], ![10, 36, 0, 0]]]
    h := ![![![-1939, 2265, 1811, 97], ![4811, -8093, -484, 0]], ![![1983, -2341, -1868, -101], ![-4920, 8338, 504, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {9} * I5N1 =  Ideal.span {B.equivFun.symm ![-73, -50, -6, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 9 ![![5, 0, 0, 0], ![-1, 1, 0, 0]]
  ![620, 285, 14, -4] ![![9, 0, 0, 0], ![-2, 1, 0, 0]] where
    su := ![![45, 0, 0, 0], ![-9, 9, 0, 0]]
    hsu := by decide
    w := ![![5580, 2565, 126, -36], ![-2772, -1278, -63, 18]]
    hw := by decide
    g := ![![![-2392430, -101678778, 51438757, -627], ![-10765986, -462937524, 5642, 0]], ![![-683565, -29051080, 14696783, -179], ![-3075994, -132267828, 1612, 0]]]
    h := ![![![414, -630, 416, -17], ![1450, -1985, 81, 0]], ![![-204, 312, -207, 8], ![-712, 990, -38, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {9} * I5N2 =  Ideal.span {B.equivFun.symm ![620, 285, 14, -4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 9 ![![7, 0, 0, 0], ![-134, -65, -4, 1]]
  ![-166, -71, -3, 1] ![![9, 0, 0, 0], ![40, 3, -1, 0]] where
    su := ![![63, 0, 0, 0], ![-1206, -585, -36, 9]]
    hsu := by decide
    w := ![![-1494, -639, -27, 9], ![-4725, -2061, -99, 27]]
    hw := by decide
    g := ![![![-1531275980408, 22016672957975, 1698145798751, -553287966412], ![344537095602, -4979591697706, 1, 0]], ![![59681833768489, -858104895823449, -66185623346034, 21564525833878], ![-13428412598279, 194080732504826, -39, 0]]]
    h := ![![![9346, -23706, -7967, 258], ![46741, 16182, 0, 0]], ![![29337, -74600, -25063, 812], ![147025, 50902, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {9} * I7N0 =  Ideal.span {B.equivFun.symm ![-166, -71, -3, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 9 ![![7, 0, 0, 0], ![-132, -70, -4, 1]]
  ![482, 264, 17, -4] ![![9, 0, 0, 0], ![-242, -174, -16, 3]] where
    su := ![![63, 0, 0, 0], ![-1188, -630, -36, 9]]
    hsu := by decide
    w := ![![4338, 2376, 153, -36], ![20853, 10881, 558, -153]]
    hw := by decide
    g := ![![![-28901, 37877, 6193, -653], ![33674, 7319, 0, 0]], ![![7627619517, -9995661973, -1634411394, 172339012], ![-8885677537, -1931229061, 70, 0]]]
    h := ![![![5066, -4458, -3541, -265], ![-46461, -16104, 0, 0]], ![![22768, -20653, -16232, -1210], ![-212794, -73749, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {9} * I7N1 =  Ideal.span {B.equivFun.symm ![482, 264, 17, -4]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0, 0], ![-130, -67, -4, 1]]
  ![-141, -67, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![33, 0, 0, 0], ![-390, -201, -12, 3]]
    hsu := by decide
    w := ![![-423, -201, -12, 3], ![1236, 603, 36, -9]]
    hw := by decide
    g := ![![![-66, 469, 126, -7], ![-862, -294, 0, 0]], ![![-6273, 13333, 4030, -199], ![-28510, -9702, 0, 0]]]
    h := ![![![63, -1036, -280, 12], ![7525, 2552, 0, 0]], ![![210, 3222, 828, -38], ![-21893, -7436, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![-141, -67, -4, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 9 ![![11, 0, 0, 0], ![-133, -67, -4, 1]]
  ![-144, -67, -4, 1] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![99, 0, 0, 0], ![-1197, -603, -36, 9]]
    hsu := by decide
    w := ![![-1296, -603, -36, 9], ![1197, 603, 36, -9]]
    hw := by decide
    g := ![![![3, -12, -4, 0], ![107, 36, 0, 0]], ![![98, 157, 34, -1], ![-802, -270, 0, 0]]]
    h := ![![![48, -145, -40, 3], ![892, 308, 0, 0]], ![![15, 153, 36, -3], ![-760, -264, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {9} * I11N1 =  Ideal.span {B.equivFun.symm ![-144, -67, -4, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 9 ![![13, 0, 0, 0], ![-136, -62, -4, 1]]
  ![341, 151, 6, -2] ![![9, 0, 0, 0], ![40, 3, -1, 0]] where
    su := ![![117, 0, 0, 0], ![-1224, -558, -36, 9]]
    hsu := by decide
    w := ![![3069, 1359, 54, -18], ![9810, 4509, 216, -63]]
    hw := by decide
    g := ![![![65306257811, -938972817306, -72422965458, 23596769663], ![-14693908052, 212370926958, -5, 0]], ![![-1057943851368, 15211107654675, 1173232604790, -382261336038], ![238037367330, -3440352024181, 81, 0]]]
    h := ![![![-87949, 315475, 109338, -2408], ![-616788, -216030, 0, 0]], ![![-280532, 1005243, 348432, -7672], ![-1965609, -688446, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {9} * I13N0 =  Ideal.span {B.equivFun.symm ![341, 151, 6, -2]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 9 ![![13, 0, 0, 0], ![-134, -70, -4, 1]]
  ![-206, -84, -2, 1] ![![9, 0, 0, 0], ![-242, -174, -16, 3]] where
    su := ![![117, 0, 0, 0], ![-1206, -630, -36, 9]]
    hsu := by decide
    w := ![![-1854, -756, -18, 9], ![-16407, -8541, -603, 135]]
    hw := by decide
    g := ![![![79259678, -103866256, -16983342, 1790803], ![-92332088, -20067492, 31, 0]], ![![-843739327, 1105683938, 180792164, -19063575], ![982899221, 213623692, -330, 0]]]
    h := ![![![-68654, 2790, 24646, 3154], ![685605, 242202, 0, 0]], ![![-601273, 24313, 215773, 27616], ![6002639, 2120544, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {9} * I13N1 =  Ideal.span {B.equivFun.symm ![-206, -84, -2, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 3 ![![17, 0, 0, 0], ![-129, -67, -4, 1]]
  ![-129, -67, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![51, 0, 0, 0], ![-387, -201, -12, 3]]
    hsu := by decide
    w := ![![-387, -201, -12, 3], ![-336, -201, -12, 3]]
    hw := by decide
    g := ![![![681, -1206, -376, 18], ![2683, 912, 0, 0]], ![![683, -1206, -376, 18], ![2682, 912, 0, 0]]]
    h := ![![![-725, -1347, -290, 13], ![11918, 4046, 0, 0]], ![![-606, -1143, -247, 11], ![10167, 3451, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {3} * I17N0 =  Ideal.span {B.equivFun.symm ![-129, -67, -4, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0, 0], ![7, 1, 0, 0]]
  ![31, 16, 2, 0] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![51, 0, 0, 0], ![21, 3, 0, 0]]
    hsu := by decide
    w := ![![93, 48, 6, 0], ![-231, -87, 6, 3]]
    hw := by decide
    g := ![![![89, 36, 1, 0], ![-39, -17, 0, 0]], ![![126, 72, 6, -1], ![-19, -8, 0, 0]]]
    h := ![![![106, -300, -52, -1], ![-253, 767, 17, 0]], ![![-287, 751, 127, 2], ![686, -1926, -33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![31, 16, 2, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 9 ![![19, 0, 0, 0], ![-131, -67, -4, 1]]
  ![-243, -134, -8, 2] ![![9, 0, 0, 0], ![-128, -67, -4, 1]] where
    su := ![![171, 0, 0, 0], ![-1179, -603, -36, 9]]
    hsu := by decide
    w := ![![-2187, -1206, -72, 18], ![-3366, -1809, -108, 27]]
    hw := by decide
    g := ![![![95, 175, 40, -1], ![-965, -324, 0, 0]], ![![71, -216, -72, 0], ![1945, 648, 0, 0]]]
    h := ![![![-117879, -203680, -40196, 3040], ![1540294, 532684, 0, 0]], ![![-181653, -313828, -61931, 4684], ![2373122, 820705, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {9} * I19N0 =  Ideal.span {B.equivFun.symm ![-243, -134, -8, 2]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 3 ![![19, 0, 0, 0], ![-132, -67, -4, 1]]
  ![-132, -67, -4, 1] ![![3, 0, 0, 0], ![-131, -67, -4, 1]] where
    su := ![![57, 0, 0, 0], ![-396, -201, -12, 3]]
    hsu := by decide
    w := ![![-396, -201, -12, 3], ![57, 0, 0, 0]]
    hw := by decide
    g := ![![![-2206, 4958, 1486, -74], ![-10487, -3570, 0, 0]], ![![21162, -44823, -13556, 669], ![95913, 32640, 0, 0]]]
    h := ![![![-11100, -21489, -4284, 363], ![154528, 53808, 0, 0]], ![![1777, 3320, 656, -56], ![-23560, -8208, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {3} * I19N1 =  Ideal.span {B.equivFun.symm ![-132, -67, -4, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 9 ![![23, 0, 0, 0], ![-131, -64, -4, 1]]
  ![464, 264, 17, -4] ![![9, 0, 0, 0], ![-242, -174, -16, 3]] where
    su := ![![207, 0, 0, 0], ![-1179, -576, -36, 9]]
    hsu := by decide
    w := ![![4176, 2376, 153, -36], ![25209, 14013, 846, -207]]
    hw := by decide
    g := ![![![-247731768450658, 324641660754605, 53082833740417, -5597270013019], ![288591315990605, 62722962911700, -48, 0]], ![![1584473472126264, -2076383269813365, -339513750751221, 35799711548561], ![-1845808017811515, -401171280729325, 307, 0]]]
    h := ![![![2189, 8760, 2451, -59], ![-36855, -12736, 0, 0]], ![![12941, 52923, 14842, -355], ![-223386, -77176, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {9} * I23N0 =  Ideal.span {B.equivFun.symm ![464, 264, 17, -4]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 9 ![![23, 0, 0, 0], ![-131, -62, -4, 1]]
  ![-148, -71, -3, 1] ![![9, 0, 0, 0], ![40, 3, -1, 0]] where
    su := ![![207, 0, 0, 0], ![-1179, -558, -36, 9]]
    hsu := by decide
    w := ![![-1332, -639, -27, 9], ![-4005, -2007, -117, 27]]
    hw := by decide
    g := ![![![-404972213555600, 5822687025201248, 449103800930272, -146326498530440], ![91118748050127, -1316938486773936, 13, 0]], ![![2803791129228949, -40312884892029939, -3109332470235150, 1013079230667997], ![-630853004077371, 9117713076011794, -90, 0]]]
    h := ![![![-1168, -13501, -4173, 59], ![43920, 15092, 0, 0]], ![![-3354, -38919, -12031, 170], ![126629, 43512, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {9} * I23N1 =  Ideal.span {B.equivFun.symm ![-148, -71, -3, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E23RS1 
