import IdealArithmetic.Examples.NF3_1_420812_2.PrimesBelow3_1_420812_2F0
import IdealArithmetic.Examples.NF3_1_420812_2.ClassGroupData3_1_420812_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![26, 0, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![26, 0, 1]] where
    su := ![![2, 0, 0], ![26, 0, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![26, 0, 1]]
    hw := by decide
    g := ![![![-6, 19, 11], ![2, 0, 2]], ![![-13, 247, 146], ![21, 0, 26]]]
    h := ![![![-6, 19, 11], ![2, 0, 2]], ![![-13, 247, 146], ![21, 0, 26]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS0 


noncomputable def E5RS0 : RelationCertificate Table 3125 ![![5, 0, 0], ![24, -2, 1]]
  ![-5256, 73, -144] ![![3125, 0, 0], ![-217, 1, 0]] where
    su := ![![15625, 0, 0], ![75000, -6250, 3125]]
    hsu := by decide
    w := ![![-16425000, 228125, -450000], ![1140625, -15625, 31250]]
    hw := by decide
    g := ![![![-4815, 1088688, -10034], ![2909, 15678124, 0]], ![![-23720, 5225684, -48163], ![5206, 75254690, 0]]]
    h := ![![![-72, -67, 12], ![-204, 0, 0]], ![![1, 5, -1], ![15, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3125} * I5N0 =  Ideal.span {B.equivFun.symm ![-5256, 73, -144]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![5, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![-5, 15, -16], ![5, 40, 0]], ![![4, -8, 8], ![1, -20, 0]]]
    h := ![![![-5, 15, -16], ![5, 40, 0]], ![![4, -8, 8], ![1, -20, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 1250 ![![7, 0, 0], ![2, 1, 0]]
  ![-219, -23, -6] ![![1250, 0, 0], ![206, 0, 1]] where
    su := ![![8750, 0, 0], ![2500, 1250, 0]]
    hsu := by decide
    w := ![![-273750, -28750, -7500], ![-45000, -3750, -1250]]
    hw := by decide
    g := ![![![-1336119944, 1748817783875569, 10409623205809], ![8107506178, -13012037082429277, -192489]], ![![-607327228, 794916908286938, 4731645327196], ![3685229964, -5914560329525803, -87495]]]
    h := ![![![907946, 2052812, 2131768], ![552675, -7461191, 0]], ![![150081, 339327, 352379], ![91362, -1233327, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {1250} * I7N0 =  Ideal.span {B.equivFun.symm ![-219, -23, -6]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E7RS0 


noncomputable def E13RS0 : RelationCertificate Table 10 ![![13, 0, 0], ![31, -2, 1]]
  ![44, -2, 1] ![![10, 0, 0], ![3, 1, 0]] where
    su := ![![130, 0, 0], ![310, -20, 10]]
    hsu := by decide
    w := ![![440, -20, 10], ![130, 0, 0]]
    hw := by decide
    g := ![![![-2169, -7635, -5184], ![-1409, 25920, 0]], ![![-5150, -18133, -12312], ![-3351, 61560, 0]]]
    h := ![![![-30, 2, -1], ![14, 0, 0]], ![![-30, 2, -1], ![13, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {10} * I13N0 =  Ideal.span {B.equivFun.symm ![44, -2, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 6250 ![![13, 0, 0], ![3, 1, 0]]
  ![3139, -87, 86] ![![6250, 0, 0], ![1456, 0, 1]] where
    su := ![![81250, 0, 0], ![18750, 6250, 0]]
    hsu := by decide
    w := ![![19618750, -543750, 537500], ![4568750, -125000, 125000]]
    hw := by decide
    g := ![![![-2323103778306, 93174165368774034875, 65708154517252638], ![9972114466904, -410675975708630231713, 2599984]], ![![-580775940458, 23293541133860541286, 16427038482392875], ![2493028599047, -102668993008905762121, 649996]]]
    h := ![![![-159298154, -525387846, -354216274], ![-77175561, 2302405824, 0]], ![![-37095368, -122345769, -82485468], ![-17971679, 536155552, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {6250} * I13N1 =  Ideal.span {B.equivFun.symm ![3139, -87, 86]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 25 ![![17, 0, 0], ![-5, 1, 0]]
  ![-122, 1, -3] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![425, 0, 0], ![-125, 25, 0]]
    hsu := by decide
    w := ![![-3050, 25, -75], ![-975, 0, -25]]
    hw := by decide
    g := ![![![37703, 369282, 92589], ![26848, -1157362, 0]], ![![-8649, -84698, -21236], ![-6153, 265450, 0]]]
    h := ![![![478, -2855, 1149], ![-304, -9768, 0]], ![![153, -912, 367], ![-96, -3120, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {25} * I17N1 =  Ideal.span {B.equivFun.symm ![-122, 1, -3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![1, 1, 0]]
  ![1, 1, 0] ![![2, 0, 0], ![26, 0, 1]] where
    su := ![![38, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![2, 2, 0], ![26, -12, 2]]
    hw := by decide
    g := ![![![43, 0, -2190], ![-251, 540, -341]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![-1, -2, -3], ![3, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![1, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-1, 1, 0]]
  ![1, -1, 0] ![![2, 0, 0], ![26, 0, 1]] where
    su := ![![38, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![2, -2, 0], ![26, 12, 0]]
    hw := by decide
    g := ![![![-20, 0, -1], ![3, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![-1, 0, 0]], ![![1, 0, 0], ![6, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![1, -1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 50 ![![23, 0, 0], ![2, 1, 0]]
  ![-97, 1, -3] ![![50, 0, 0], ![-17, 1, 0]] where
    su := ![![1150, 0, 0], ![100, 50, 0]]
    hsu := by decide
    w := ![![-4850, 50, -150], ![1650, 0, 50]]
    hw := by decide
    g := ![![![-55592, 1191363, -140261], ![42761, 3506524, 0]], ![![-11378, 244131, -28742], ![8803, 718550, 0]]]
    h := ![![![344, 706, 709], ![73, -8155, 0]], ![![-119, -241, -241], ![-1, 2772, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {50} * I23N1 =  Ideal.span {B.equivFun.symm ![-97, 1, -3]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 3125 ![![31, 0, 0], ![-2, 1, 0]]
  ![2117, 14, 58] ![![3125, 0, 0], ![-217, 1, 0]] where
    su := ![![96875, 0, 0], ![-6250, 3125, 0]]
    hsu := by decide
    w := ![![6615625, 43750, 181250], ![-459375, -3125, -12500]]
    hw := by decide
    g := ![![![32015, -6991522, 64438], ![-2938, -100684374, 0]], ![![-1357, 338302, -3118], ![2909, 4871874, 0]]]
    h := ![![![-11100, 22479, -22524], ![1467, 349151, 0]], ![![771, -1561, 1564], ![-98, -24244, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {3125} * I31N1 =  Ideal.span {B.equivFun.symm ![2117, 14, 58]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E31RS1 
