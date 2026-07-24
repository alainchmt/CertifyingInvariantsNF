import IdealArithmetic.Examples.NF3_1_387059_1.PrimesBelow3_1_387059_1F1
import IdealArithmetic.Examples.NF3_1_387059_1.ClassGroupData3_1_387059_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![-14, 1, 0]]
  ![-58, 1, -2] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![74, 0, 0], ![-28, 2, 0]]
    hsu := by decide
    w := ![![-116, 2, -4], ![-72, 2, -2]]
    hw := by decide
    g := ![![![647, -1463, 166], ![-407, 0, -111]], ![![-246, 553, -63], ![156, 0, 42]]]
    h := ![![![-74, 681, -182], ![49, 1683, 0]], ![![-34, 422, -113], ![62, 1045, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![-58, 1, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 2 ![![41, 0, 0], ![14, 1, 0]]
  ![60, -1, 2] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![82, 0, 0], ![28, 2, 0]]
    hsu := by decide
    w := ![![120, -2, 4], ![74, 0, 2]]
    hw := by decide
    g := ![![![-48493, 109456, -12470], ![30482, 0, 8313]], ![![-17116, 38631, -4401], ![10760, 0, 2934]]]
    h := ![![![36, 343, 106], ![54, -1086, 0]], ![![17, 210, 65], ![48, -666, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![60, -1, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 32 ![![43, 0, 0], ![-18, 1, 0]]
  ![-2470, 37, -84] ![![32, 0, 0], ![-9, 1, 0]] where
    su := ![![1376, 0, 0], ![-576, 32, 0]]
    hsu := by decide
    w := ![![-79040, 1184, -2688], ![21632, -320, 736]]
    hw := by decide
    g := ![![![39872126628814501, -224423112755434464, 89997085855061910], ![-18227257887961383, -719976686754170966, 49328181]], ![![-16690759510368899, 93945132107961812, -37673428624078460], ![7630061490665064, 301387428956491700, -20649132]]]
    h := ![![![-3739768, 45940360, -9684552], ![2633904, 104108913, 0]], ![![1023520, -12573076, 2650493], ![-720828, -28492794, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {32} * I43N1 =  Ideal.span {B.equivFun.symm ![-2470, 37, -84]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 128 ![![47, 0, 0], ![18, 1, 0]]
  ![-2, -25, 4] ![![128, 0, 0], ![-9, 1, 0]] where
    su := ![![6016, 0, 0], ![2304, 128, 0]]
    hsu := by decide
    w := ![![-256, -3200, 512], ![0, 128, -128]]
    hw := by decide
    g := ![![![-73404637867, 370479457624, -149522530473], ![8055634419, 4769328949935, -8795442969]], ![![-28112017141, 141883744223, -57263138435], ![3085093010, 1826525695079, -3368419908]]]
    h := ![![![-8936, -93268, -21972], ![-5353, 258172, 0]], ![![-208, -2169, -511], ![-124, 6004, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {128} * I47N1 =  Ideal.span {B.equivFun.symm ![-2, -25, 4]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E47RS1 


noncomputable def E53RS0 : RelationCertificate Table 128 ![![53, 0, 0], ![11, 1, 0]]
  ![-6, 53, 12] ![![128, 0, 0], ![-9, 1, 0]] where
    su := ![![6784, 0, 0], ![1408, 128, 0]]
    hsu := by decide
    w := ![![-768, 6784, 1536], ![256, -896, 128]]
    hw := by decide
    g := ![![![-141102916, 586916237, 0], ![14506683, 2768307893, 1581890205]], ![![-29285459, 121812614, 0], ![3010905, 574553576, 328316325]]]
    h := ![![![164, 899, 360], ![76, -4767, 0]], ![![-55, -258, -103], ![17, 1365, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {128} * I53N0 =  Ideal.span {B.equivFun.symm ![-6, 53, 12]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 4 ![![53, 0, 0], ![-6, 1, 0]]
  ![-6, 1, 0] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![212, 0, 0], ![-24, 4, 0]]
    hsu := by decide
    w := ![![-24, 4, 0], ![8, -8, 4]]
    hw := by decide
    g := ![![![-23784622, 112640341, -4038897], ![34106245, 0, 16155587]], ![![2694080, -12758749, 457485], ![-3863204, 0, -1829940]]]
    h := ![![![-1838, 6573, -3760], ![372, 49820, 0]], ![![628, -2233, 1277], ![-93, -16920, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {4} * I53N1 =  Ideal.span {B.equivFun.symm ![-6, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 32 ![![59, 0, 0], ![-23, 1, 0]]
  ![-1290, 19, -44] ![![32, 0, 0], ![-9, 1, 0]] where
    su := ![![1888, 0, 0], ![-736, 32, 0]]
    hsu := by decide
    w := ![![-41280, 608, -1408], ![11296, -160, 384]]
    hw := by decide
    g := ![![![12144285, -68660684, 28089731], ![-5561205, -223079283, 936324]], ![![-4701006, 26578328, -10873444], ![2152751, 86353269, -362448]]]
    h := ![![![-7176, 107533, -17936], ![4652, 264545, 0]], ![![1980, -29426, 4908], ![-1231, -72390, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {32} * I59N1 =  Ideal.span {B.equivFun.symm ![-1290, 19, -44]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E59RS1 


noncomputable def E61RS0 : RelationCertificate Table 4 ![![61, 0, 0], ![6, 1, 0]]
  ![6, 1, 0] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![244, 0, 0], ![24, 4, 0]]
    hsu := by decide
    w := ![![24, 4, 0], ![-4, 4, 4]]
    hw := by decide
    g := ![![![-298, 1457, -52], ![440, 0, 209]], ![![-34, 167, -6], ![52, 0, 24]]]
    h := ![![![214, 549, 440], ![62, -6710, 0]], ![![-39, -94, -75], ![15, 1144, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {4} * I61N0 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E61RS0 


noncomputable def E61RS2 : RelationCertificate Table 512 ![![61, 0, 0], ![-22, 1, 0]]
  ![318, 7, 4] ![![512, 0, 0], ![119, 1, 0]] where
    su := ![![31232, 0, 0], ![-11264, 512, 0]]
    hsu := by decide
    w := ![![162816, 3584, 2048], ![37888, 1024, 512]]
    hw := by decide
    g := ![![![-78117969297413, -4991770831747844, -169167044548105], ![-27905877301013, 21659394984293287, -198786186309]], ![![28173713964924, 1800312077454023, 61011108817373], ![10064421951886, -7811590654877251, 71693429868]]]
    h := ![![![9659932, -134597106, 23424416], ![-5690416, -357222343, 0]], ![![2247602, -31316974, 5450205], ![-1323982, -83115626, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {512} * I61N2 =  Ideal.span {B.equivFun.symm ![318, 7, 4]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E61RS2 


noncomputable def E67RS0 : RelationCertificate Table 512 ![![67, 0, 0], ![-28, 1, 0]]
  ![70, -21, -12] ![![512, 0, 0], ![119, 1, 0]] where
    su := ![![34304, 0, 0], ![-14336, 512, 0]]
    hsu := by decide
    w := ![![35840, -10752, -6144], ![8192, -2048, -1536]]
    hw := by decide
    g := ![![![-79503990810035443, -5080134342003252424, -172209829530680495], ![-28400604000775823, 22042857494822950441, 22648071171]], ![![33225555580542085, 2123041676488323248, 71968302525325265], ![11868911700337568, -9211942436929388719, -9464867610]]]
    h := ![![![3067120, -57399453, 7921568], ![-2138413, -132686267, 0]], ![![700436, -13108013, 1809007], ![-488305, -30300868, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {512} * I67N0 =  Ideal.span {B.equivFun.symm ![70, -21, -12]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 16 ![![67, 0, 0], ![-12, 1, 0]]
  ![126, -1, 4] ![![16, 0, 0], ![7, 1, 0]] where
    su := ![![1072, 0, 0], ![-192, 16, 0]]
    hsu := by decide
    w := ![![2016, -16, 64], ![912, 0, 32]]
    hw := by decide
    g := ![![![11466379, 46847312, 30210550], ![7944509, -122520561, 745938]], ![![-1845171, -7538649, -4861468], ![-1278412, 19715953, -120036]]]
    h := ![![![147802, -1008350, 310452], ![-41461, -5200070, 0]], ![![66855, -456066, 140414], ![-18720, -2351934, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {16} * I67N1 =  Ideal.span {B.equivFun.symm ![126, -1, 4]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 128 ![![71, 0, 0], ![27, 1, 0]]
  ![2, -39, -4] ![![128, 0, 0], ![-9, 1, 0]] where
    su := ![![9088, 0, 0], ![3456, 128, 0]]
    hsu := by decide
    w := ![![256, -4992, -512], ![-128, 512, -128]]
    hw := by decide
    g := ![![![35691661971458, -179803845669243, 71933769417985], ![-3914287526620, -2301880633144170, -6724935]], ![![13697881081431, -69005800232274, 27607014210047], ![-1502240077758, -883424459238121, -2580921]]]
    h := ![![![28826, 461123, 70980], ![17524, -1259896, 0]], ![![-11213, -179142, -27575], ![-6770, 489456, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {128} * I71N1 =  Ideal.span {B.equivFun.symm ![2, -39, -4]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 1024 ![![73, 0, 0], ![1, 1, 0]]
  ![-5350, 69, -180] ![![1024, 0, 0], ![119, 1, 0]] where
    su := ![![74752, 0, 0], ![1024, 1024, 0]]
    hsu := by decide
    w := ![![-5478400, 70656, -184320], ![-637952, 8192, -21504]]
    hw := by decide
    g := ![![![-396713940664, -23882062215252, -809563729243], ![-69424824676, 207248314688479, -75]], ![![-26417695461, -1590337469557, -53909897772], ![-4623088298, 13800933829784, -5]]]
    h := ![![![11090613, -2080, 22185532], ![151909, -404886004, 0]], ![![1291414, -243, 2583331], ![17747, -47145796, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {1024} * I73N1 =  Ideal.span {B.equivFun.symm ![-5350, 69, -180]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![21, 1, 0]]
  ![472, -7, 16] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![158, 0, 0], ![42, 2, 0]]
    hsu := by decide
    w := ![![944, -14, 32], ![586, -8, 20]]
    hw := by decide
    g := ![![![-176400, 398158, -45363], ![110879, 0, 30240]], ![![-47776, 107835, -12286], ![30031, 0, 8190]]]
    h := ![![![88365, 978664, 195824], ![35937, -3867520, 0]], ![![54854, 607507, 121558], ![22303, -2400768, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![472, -7, 16]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 
