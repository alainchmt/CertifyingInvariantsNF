import IdealArithmetic.Examples.NF3_1_161700_2.PrimesBelow3_1_161700_2F0
import IdealArithmetic.Examples.NF3_1_161700_2.ClassGroupData3_1_161700_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 0, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![2, 0, 0], ![1, 0, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 0, 1]]
    hw := by decide
    g := ![![![0, 0, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, 0, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![3696505, -352313, -123891] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![7393010, -704626, -247782], ![-22173326, -1258270, 3820396]]
    hw := by decide
    g := ![![![2503071206589, 375465876128, -262662251189], ![1120204477702, -3, 0]], ![![10730602264196, 1609612611129, -1126026355064], ![4802287954567, 0, 0]]]
    h := ![![![5616675, -1363374, 0], ![2126653, 0, -123891]], ![![-66966817, 14669867, 0], ![-26148473, 0, 1910198]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![3696505, -352313, -123891]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 2 ![![3, 0, 0], ![1, 0, 1]]
  ![-22, 4, -1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![6, 0, 0], ![2, 0, 2]]
    hsu := by decide
    w := ![![-44, 8, -2], ![-78, -16, 24]]
    hw := by decide
    g := ![![![-412, -41, -40], ![-19, 0, 0]], ![![-1277, -126, -124], ![-61, 0, 0]]]
    h := ![![![87, 0, -10], ![29, -4, 0]], ![![-202, 0, 23], ![-57, 8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![-22, 4, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 2 ![![3, 0, 0], ![-1, 1, 0]]
  ![31099403195, 3811982859, 3019811404] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![6, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![62198806390, 7623965718, 6039622808], ![235545289512, 28871763246, 22871897154]]
    hw := by decide
    g := ![![![-226017, 12521, 12951], ![6261, 0, 0]], ![![412065, -67179, 26986], ![-33588, 0, 0]]]
    h := ![![![1386053173392, 104716818078, -18455670709], ![-427112118437, 0, -58386823531]], ![![5248947929298, 396559912683, -69891153104], ![-1617462672204, 0, -221109407889]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {2} * I3N1 =  Ideal.span {B.equivFun.symm ![31099403195, 3811982859, 3019811404]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 2 ![![5, 0, 0], ![-2, 1, 0]]
  ![109, 13, -25] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![10, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![218, 26, -50], ![1448, -338, 134]]
    hw := by decide
    g := ![![![-9945, -1696, 926], ![-4509, -38, 0]], ![![-11846, -1879, 1184], ![-5330, -19, 0]]]
    h := ![![![23, 43, -251], ![3, 205, 0]], ![![146, 289, -1927], ![3, 1617, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2} * I5N0 =  Ideal.span {B.equivFun.symm ![109, 13, -25]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![2, 1, 0]]
  ![-41, -5, -4] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![-82, -10, -8], ![-312, -38, -30]]
    hw := by decide
    g := ![![![3, -2, 1], ![1, 0, 0]], ![![12, 0, -1], ![-1, 0, 0]]]
    h := ![![![-77, -44, -16], ![249, 18, 0]], ![![-280, -156, -51], ![902, 57, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-41, -5, -4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0], ![-5, 1, 0]]
  ![9, 1, -2] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![22, 0, 0], ![-10, 2, 0]]
    hsu := by decide
    w := ![![18, 2, -4], ![-156, 14, 6]]
    hw := by decide
    g := ![![![-175, -18, -17], ![-7, 0, 0]], ![![-41, -4, -4], ![-2, 0, 0]]]
    h := ![![![4, 18, -28], ![7, 51, 0]], ![![-8, -177, 267], ![-2, -489, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![9, 1, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![-2, 1, 0]]
  ![1533177033, 187927869, 148874416] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![22, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![3066354066, 375855738, 297748832], ![11612204448, 1423356070, 1127567214]]
    hw := by decide
    g := ![![![71345, 420, -9077], ![211, 0, 0]], ![![-77336, 6470, 1937], ![3237, 0, 0]]]
    h := ![![![146016861, 693580086, -4065351760], ![36504219, 7477957296, 0]], ![![552962118, 2626570053, -15395383173], ![138240537, 28318833085, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![1533177033, 187927869, 148874416]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![8, 1, 0]]
  ![-1, -1, 1] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![38, 0, 0], ![16, 2, 0]]
    hsu := by decide
    w := ![![-2, -2, 2], ![-92, 14, -2]]
    hw := by decide
    g := ![![![-73146, 1122, 14627], ![-29259, 2250, 0]], ![![-31705, 485, 6339], ![-12682, 975, 0]]]
    h := ![![![-19, -10, -5], ![45, 16, 0]], ![![-250, -50, -13], ![588, 41, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![-1, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-8, 1, 0]]
  ![-19617769, 3205239, -561375] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![38, 0, 0], ![-16, 2, 0]]
    hsu := by decide
    w := ![![-39235538, 6410478, -1122750], ![237688748, -10503114, -19056394]]
    hw := by decide
    g := ![![![-111625926924412, -16744120717254, 11713576977837], ![-49956174973287, 450, 0]], ![![2503071208929, 375465876092, -262662251657], ![1120204478638, -75, 0]]]
    h := ![![![-315116427, 42924441, -3025479], ![-745949293, 9487121, 0]], ![![1903121698, -258704946, 17772979], ![4505058486, -57869133, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![-19617769, 3205239, -561375]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 2 ![![19, 0, 0], ![-1, 1, 0]]
  ![-237, -29, -23] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![38, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![-474, -58, -46], ![-2200, -270, -214]]
    hw := by decide
    g := ![![![-1774, 26, 357], ![-707, 54, 0]], ![![110, -3, -23], ![45, -3, 0]]]
    h := ![![![-24, 10, -5], ![-219, 12, 0]], ![![-114, 49, -11], ![-1066, 17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {2} * I19N2 =  Ideal.span {B.equivFun.symm ![-237, -29, -23]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS2 


noncomputable def E23RS0 : RelationCertificate Table 2 ![![23, 0, 0], ![-11, 1, 0]]
  ![9, 1, 1] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![46, 0, 0], ![-22, 2, 0]]
    hsu := by decide
    w := ![![18, 2, 2], ![74, 12, 8]]
    hw := by decide
    g := ![![![112383, -1728, -22477], ![44953, -3458, 0]], ![![-50278, 773, 10056], ![-20111, 1547, 0]]]
    h := ![![![9, 51, -31], ![18, 119, 0]], ![![15, 206, -124], ![28, 476, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {2} * I23N0 =  Ideal.span {B.equivFun.symm ![9, 1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![-10, 1, 0]]
  ![2049, 125, -361] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![46, 0, 0], ![-20, 2, 0]]
    hsu := by decide
    w := ![![4098, 250, -722], ![16492, -4818, 2410]]
    hw := by decide
    g := ![![![-2319819, -360695, 236122], ![-1041847, -2366, 0]], ![![220274, 38422, -20022], ![100126, 1001, 0]]]
    h := ![![![22933, -2358, 37], ![52541, -202, 0]], ![![93782, -9739, 247], ![214874, -746, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![2049, 125, -361]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 2 ![![23, 0, 0], ![-3, 1, 0]]
  ![9939, 363, -1529] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![46, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![19878, 726, -3058], ![58130, -20240, 11468]]
    hw := by decide
    g := ![![![-44574444, -6697020, 4671278], ![-19951583, -2002, 0]], ![![-8880298, -1331574, 932144], ![-3974077, 91, 0]]]
    h := ![![![15831, -5141, 5], ![118058, -274, 0]], ![![46661, -15634, 434], ![348046, -708, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {2} * I23N2 =  Ideal.span {B.equivFun.symm ![9939, 363, -1529]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS2 


noncomputable def E31RS1 : RelationCertificate Table 2 ![![31, 0, 0], ![-4, 1, 0]]
  ![1896, -6, -223] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![62, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![3792, -12, -446], ![-17394, 2336, -36]]
    hw := by decide
    g := ![![![2683490, 263141, 260572], ![131571, 0, 0]], ![![309376, 30337, 30041], ![15169, 0, 0]]]
    h := ![![![3816, -942, -1], ![29100, -32, 0]], ![![-17527, 4370, -42], ![-133660, 214, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {2} * I31N1 =  Ideal.span {B.equivFun.symm ![1896, -6, -223]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 
