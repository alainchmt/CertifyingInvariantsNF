import IdealArithmetic.Examples.NF3_1_892863_2.PrimesBelow3_1_892863_2F0
import IdealArithmetic.Examples.NF3_1_892863_2.ClassGroupData3_1_892863_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 32 ![![2, 0, 0], ![0, 1, 0]]
  ![29, 1, 1] ![![32, 0, 0], ![175, 13, 10]] where
    su := ![![64, 0, 0], ![0, 32, 0]]
    hsu := by decide
    w := ![![928, 32, 32], ![7648, 384, 224]]
    hw := by decide
    g := ![![![246, -1046, -230], ![1471, -175, 0]], ![![-61, -260, -62], ![375, -42, 0]]]
    h := ![![![123987, -39464, -25191], ![17461, 12139, -1827]], ![![1021824, -325222, -207609], ![143875, 100042, -15057]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {32} * I2N0 =  Ideal.span {B.equivFun.symm ![29, 1, 1]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![18, 1, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![18, 1, 1]] where
    su := ![![2, 0, 0], ![18, 1, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![18, 1, 1]]
    hw := by decide
    g := ![![![-10, -17, -6], ![18, -2, 0]], ![![27, -146, -47], ![149, -18, 0]]]
    h := ![![![-10, -17, -6], ![18, -2, 0]], ![![27, -146, -47], ![149, -18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 1 ![![2, 0, 0], ![18, 2, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![18, 2, 1]] where
    su := ![![2, 0, 0], ![18, 2, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![18, 2, 1]]
    hw := by decide
    g := ![![![-8, -25, -2], ![18, -2, 0]], ![![27, -213, -12], ![151, -18, 0]]]
    h := ![![![-8, -25, -2], ![18, -2, 0]], ![![27, -213, -12], ![151, -18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {1} * I2N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS2 


noncomputable def E5RS0 : RelationCertificate Table 4 ![![5, 0, 0], ![19, 2, 1]]
  ![-1969, -87, -61] ![![4, 0, 0], ![37, 3, 2]] where
    su := ![![20, 0, 0], ![76, 8, 4]]
    hsu := by decide
    w := ![![-7876, -348, -244], ![-115832, -5116, -3588]]
    hw := by decide
    g := ![![![-421, 2227, 353], ![-1877, 234, 0]], ![![-1564, 8542, 1360], ![-7202, 897, 0]]]
    h := ![![![-29, 21, 7], ![-96, 0, 0]], ![![-426, 309, 103], ![-1412, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {4} * I5N0 =  Ideal.span {B.equivFun.symm ![-1969, -87, -61]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 16 ![![5, 0, 0], ![-2, 1, 0]]
  ![29, -7, 1] ![![16, 0, 0], ![103, 1, 6]] where
    su := ![![80, 0, 0], ![-32, 16, 0]]
    hsu := by decide
    w := ![![464, -112, 16], ![-3664, 672, 128]]
    hw := by decide
    g := ![![![-19, -27, -20], ![47, -6, 0]], ![![-20, 3, 3], ![-10, 1, 0]]]
    h := ![![![-21, 12, -63], ![12, 79, 0]], ![![-249, 110, -504], ![124, 632, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {16} * I5N1 =  Ideal.span {B.equivFun.symm ![29, -7, 1]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E5RS1 


noncomputable def E11RS0 : RelationCertificate Table 4 ![![11, 0, 0], ![16, 0, 1]]
  ![-125, 11, 19] ![![4, 0, 0], ![20, 1, 1]] where
    su := ![![44, 0, 0], ![64, 0, 4]]
    hsu := by decide
    w := ![![-500, 44, 76], ![320, 132, -244]]
    hw := by decide
    g := ![![![-12142, 24278, 7711], ![-52617, 7350, 0]], ![![-17581, 35259, 11187], ![-76273, 10675, 0]]]
    h := ![![![-7, 1, 2], ![-3, 0, 0]], ![![0, 3, -6], ![5, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {4} * I11N0 =  Ideal.span {B.equivFun.symm ![-125, 11, 19]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 16 ![![11, 0, 0], ![1, 1, 0]]
  ![-289781, 45191, 20023] ![![16, 0, 0], ![12, 1, 1]] where
    su := ![![176, 0, 0], ![16, 16, 0]]
    hsu := by decide
    w := ![![-4636496, 723056, 320368], ![4567872, -582064, -474576]]
    hw := by decide
    g := ![![![-1853789093, -40972800, -2723304], ![-1393072817, 94, 0]], ![![-961265504, -21246125, -1412149], ![-722365255, 9, 0]]]
    h := ![![![-36907, -6455, -20023], ![-3942, 60069, 0]], ![![41685, 12424, 29661], ![4923, -88983, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {16} * I11N1 =  Ideal.span {B.equivFun.symm ![-289781, 45191, 20023]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 16 ![![13, 0, 0], ![0, 1, 0]]
  ![-16367, -723, -507] ![![16, 0, 0], ![103, 1, 6]] where
    su := ![![208, 0, 0], ![0, 16, 0]]
    hsu := by decide
    w := ![![-261872, -11568, -8112], ![-2141456, -94592, -66336]]
    hw := by decide
    g := ![![![-5, 12, 7], ![-19, 2, 0]], ![![-43, 12, 9], ![-20, 3, 0]]]
    h := ![![![507377, 252766, 1017233], ![19453, -3306134, 0]], ![![4149071, 2066997, 8318414], ![159009, -27035882, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {16} * I13N0 =  Ideal.span {B.equivFun.symm ![-16367, -723, -507]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 8 ![![13, 0, 0], ![5, 1, 0]]
  ![-2143135323, -94669007, -66388367] ![![8, 0, 0], ![20, 1, 1]] where
    su := ![![104, 0, 0], ![40, 8, 0]]
    hsu := by decide
    w := ![![-17145082584, -757352056, -531106936], ![-61207416904, -2703723520, -1896035408]]
    hw := by decide
    g := ![![![1153, -1948, -567], ![2621, 50, 0]], ![![24, 368, -592], ![49, 21, 0]]]
    h := ![![![8196707366, 31044204718, 20980017605], ![5540595507, -68201654308, 0]], ![![29261992908, 110826854949, 74898016846], ![19779755359, -243477805856, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {8} * I13N1 =  Ideal.span {B.equivFun.symm ![-2143135323, -94669007, -66388367]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 32 ![![13, 0, 0], ![-5, 1, 0]]
  ![3, -1, -1] ![![32, 0, 0], ![175, 13, 10]] where
    su := ![![416, 0, 0], ![-160, 32, 0]]
    hsu := by decide
    w := ![![96, -32, -32], ![-2048, 32, 96]]
    hw := by decide
    g := ![![![2071, -6232, -1346], ![8717, -1050, 0]], ![![-909, 2274, 485], ![-3169, 385, 0]]]
    h := ![![![841, -2007, 2043], ![-470, -6640, 0]], ![![-16818, 40253, -40989], ![9572, 133215, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {32} * I13N2 =  Ideal.span {B.equivFun.symm ![3, -1, -1]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E13RS2 


noncomputable def E17RS1 : RelationCertificate Table 16 ![![17, 0, 0], ![2, 1, 0]]
  ![151563, 6695, 4695] ![![16, 0, 0], ![12, 1, 1]] where
    su := ![![272, 0, 0], ![32, 16, 0]]
    hsu := by decide
    w := ![![2425008, 107120, 75120], ![3116096, 137648, 96528]]
    hw := by decide
    g := ![![![6713376, -1275866, -102189], ![4948927, -1104646, 0]], ![![1030783, -195898, -15688], ![759866, -169611, 0]]]
    h := ![![![-1238319, -1900750, -2554777], ![-257483, 10858976, 0]], ![![-1591220, -2442433, -3282847], ![-330860, 13953608, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {16} * I17N1 =  Ideal.span {B.equivFun.symm ![151563, 6695, 4695]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![6, 1, 0]]
  ![-337377, -14903, -10451] ![![2, 0, 0], ![18, 1, 1]] where
    su := ![![38, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![-674754, -29806, -20902], ![-8960650, -395820, -277576]]
    hw := by decide
    g := ![![![-4103, 22020, 7093], ![-22251, 2700, 0]], ![![-1483, 7891, 2570], ![-8016, 975, 0]]]
    h := ![![![-1472619, -5909713, -3400421], ![-776065, 16149387, 0]], ![![-19556165, -78480255, -45157172], ![-10306155, 214461870, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![-337377, -14903, -10451]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-4, 1, 0]]
  ![33113950, 1462747, 1025778] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![38, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![66227900, 2925494, 2051556], ![188880366, 8343438, 5850988]]
    hw := by decide
    g := ![![![5552, -1969, -364], ![1793, 0, 0]], ![![-3776, 1575, -130], ![-1098, 0, 0]]]
    h := ![![![1376099198, -2167719549, 2918785902], ![-403795592, -13863976590, 0]], ![![3924601565, -6182283626, 8324306666], ![-1151615257, -39539725290, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![33113950, 1462747, 1025778]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 16 ![![19, 0, 0], ![-2, 1, 0]]
  ![-1380137, 116107, 216291] ![![16, 0, 0], ![103, 1, 6]] where
    su := ![![304, 0, 0], ![-32, 16, 0]]
    hsu := by decide
    w := ![![-22082192, 1857712, 3460656], ![-120096528, 43146624, -21490496]]
    hw := by decide
    g := ![![![9751914430, 13700395936, -10199489186], ![59809416033, 5500, 0]], ![![1387828678, 1949741871, -1451526983], ![8511683618, -625, 0]]]
    h := ![![![-184093, 61838, -216291], ![22640, 1081455, 0]], ![![307307, -209251, 1343156], ![-43347, -6715780, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {16} * I19N2 =  Ideal.span {B.equivFun.symm ![-1380137, 116107, 216291]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E19RS2 


noncomputable def E23RS1 : RelationCertificate Table 8 ![![23, 0, 0], ![0, 1, 0]]
  ![-114789429, -5070609, -3555857] ![![8, 0, 0], ![20, 1, 1]] where
    su := ![![184, 0, 0], ![0, 8, 0]]
    hsu := by decide
    w := ![![-918315432, -40564872, -28446856], ![-3278357816, -144815344, -101554400]]
    hw := by decide
    g := ![![![-371554, 214978, 60048], ![-894477, 138274, 0]], ![![-19712, 11409, 3073], ![-47428, 7355, 0]]]
    h := ![![![1721841435, 861567007, 3453509957], ![37459447, -19858571217, 0]], ![![6146920905, 3075767687, 12328924208], ![133729052, -70894487771, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {8} * I23N1 =  Ideal.span {B.equivFun.symm ![-114789429, -5070609, -3555857]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 16 ![![29, 0, 0], ![-8, 1, 0]]
  ![-615, -27, -19] ![![16, 0, 0], ![103, 1, 6]] where
    su := ![![464, 0, 0], ![-128, 16, 0]]
    hsu := by decide
    w := ![![-9840, -432, -304], ![-80336, -3552, -2496]]
    hw := by decide
    g := ![![![-837888, 2250486, 1786362], ![-4583029, 541806, 0]], ![![212244, -570330, -452714], ![1161468, -137307, 0]]]
    h := ![![![-1383, 5310, -3047], ![585, 22086, 0]], ![![-11329, 43356, -24876], ![4638, 180312, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {16} * I29N1 =  Ideal.span {B.equivFun.symm ![-615, -27, -19]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 8 ![![31, 0, 0], ![-6, 1, 0]]
  ![-18291711331, -808002243, -566626303] ![![8, 0, 0], ![-33, 1, -2]] where
    su := ![![248, 0, 0], ![-48, 8, 0]]
    hsu := by decide
    w := ![![-146333690648, -6464017944, -4533010424], ![658641589376, 29094264168, 20402883144]]
    hw := by decide
    g := ![![![-179898, 134728, 240853], ![698741, -83244, 0]], ![![28854, -23005, -39382], ![-111970, 12883, 0]]]
    h := ![![![1364621741537, -3584556088722, 2877405771455], ![-379751178621, -22300036385352, 0]], ![![-6142103221478, 16133931352568, -12951078471393], ![1709243570383, 100371495743394, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {8} * I31N1 =  Ideal.span {B.equivFun.symm ![-18291711331, -808002243, -566626303]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E31RS1 
