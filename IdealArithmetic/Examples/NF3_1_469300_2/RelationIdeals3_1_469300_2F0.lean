import IdealArithmetic.Examples.NF3_1_469300_2.PrimesBelow3_1_469300_2F0
import IdealArithmetic.Examples.NF3_1_469300_2.ClassGroupData3_1_469300_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 32 ![![2, 0, 0], ![0, 1, 0]]
  ![4, 1, 0] ![![32, 0, 0], ![-47, -4, 1]] where
    su := ![![64, 0, 0], ![0, 32, 0]]
    hsu := by decide
    w := ![![128, 32, 0], ![192, 32, 0]]
    hw := by decide
    g := ![![![-1, 0, 0], ![1, 0, 0]], ![![3, 0, 0], ![-2, 0, 0]]]
    h := ![![![2, 0, 0], ![1, 0, 0]], ![![3, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {32} * I2N0 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 10*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 36 ![![3, 0, 0], ![-64, -5, 1]]
  ![-8, -7, -1] ![![36, 0, 0], ![-61, -6, 1]] where
    su := ![![108, 0, 0], ![-2304, -180, 36]]
    hsu := by decide
    w := ![![-288, -252, -36], ![108, 0, 0]]
    hw := by decide
    g := ![![![354, 23, -5], ![-575, -126, 0]], ![![-6844, -435, 96], ![11748, 2534, 0]]]
    h := ![![![40, 1, -1], ![2, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {36} * I3N0 =  Ideal.span {B.equivFun.symm ![-8, -7, -1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 64 ![![3, 0, 0], ![-1, 1, 0]]
  ![4, 1, 0] ![![192, 0, 0], ![-15, -4, 1]] where
    su := ![![192, 0, 0], ![-64, 64, 0]]
    hsu := by decide
    w := ![![768, 192, 0], ![320, 64, 0]]
    hw := by decide
    g := ![![![-1, 0, 0], ![3, 0, 0]], ![![7, 1, 0], ![-17, -3, 0]]]
    h := ![![![10, -5, 0], ![18, 0, 0]], ![![4, -2, 0], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {64} * I3N1 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 11*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 18 ![![5, 0, 0], ![0, 1, 0]]
  ![110, 13, -2] ![![18, 0, 0], ![-61, -6, 1]] where
    su := ![![90, 0, 0], ![0, 18, 0]]
    hsu := by decide
    w := ![![1980, 234, -36], ![2790, 162, -36]]
    hw := by decide
    g := ![![![-1042, 18, 9], ![3679, 640, 0]], ![![11, 2, 0], ![2, 0, 0]]]
    h := ![![![22, 2, 0], ![3, -2, 0]], ![![31, 2, -1], ![-1, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {18} * I5N0 =  Ideal.span {B.equivFun.symm ![110, 13, -2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E11RS0 : RelationCertificate Table 4 ![![11, 0, 0], ![1, 1, 0]]
  ![72, 5, -1] ![![4, 0, 0], ![-61, -6, 1]] where
    su := ![![44, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![288, 20, -4], ![-212, -72, 8]]
    hw := by decide
    g := ![![![444, -689, 43], ![-5391, -870, 0]], ![![85, -63, 4], ![-537, -87, 0]]]
    h := ![![![12, 5, -1], ![-60, 10, 0]], ![![-5, -5, -3], ![2, 35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {4} * I11N0 =  Ideal.span {B.equivFun.symm ![72, 5, -1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 24 ![![11, 0, 0], ![2, 1, 0]]
  ![-44, -13, -1] ![![24, 0, 0], ![-437, -32, 7]] where
    su := ![![264, 0, 0], ![48, 24, 0]]
    hsu := by decide
    w := ![![-1056, -312, -24], ![-3192, -1176, -120]]
    hw := by decide
    g := ![![![90, -4, -5], ![53, 8, 0]], ![![424, 24, -9], ![54, 5, 0]]]
    h := ![![![-1704, -885, -17], ![9350, 186, 0]], ![![-5157, -2678, -51], ![28297, 556, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {24} * I11N1 =  Ideal.span {B.equivFun.symm ![-44, -13, -1]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 144 ![![11, 0, 0], ![-3, 1, 0]]
  ![428, 19, -5] ![![144, 0, 0], ![4277, 452, -67]] where
    su := ![![1584, 0, 0], ![-432, 144, 0]]
    hsu := by decide
    w := ![![61632, 2736, -720], ![488016, 66384, -9648]]
    hw := by decide
    g := ![![![105075, -704821, -64803], ![1014779, 171066, 0]], ![![87211, -587388, -53997], ![845661, 142555, 0]]]
    h := ![![![652, -213, 3], ![2248, -38, 0]], ![![5131, -1653, 23], ![17684, -320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {144} * I11N2 =  Ideal.span {B.equivFun.symm ![428, 19, -5]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 16 ![![13, 0, 0], ![1, 1, 0]]
  ![12, -1, 0] ![![16, 0, 0], ![-63, -4, 1]] where
    su := ![![208, 0, 0], ![16, 16, 0]]
    hsu := by decide
    w := ![![192, -16, 0], ![-1136, -80, 16]]
    hw := by decide
    g := ![![![7, 1, 0], ![1, 0, 0]], ![![6, 1, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![12, 0, 0]], ![![-6, -6, -5], ![7, 66, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {16} * I13N0 =  Ideal.span {B.equivFun.symm ![12, -1, 0]} * (J0 ^ 8*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_0 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 2 ![![13, 0, 0], ![6, 1, 0]]
  ![6, 1, 0] ![![2, 0, 0], ![-63, -6, 1]] where
    su := ![![26, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![12, 2, 0], ![2, -4, 0]]
    hw := by decide
    g := ![![![2, 0, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![18, 3, 0], ![-38, 0, 0]], ![![1, 0, 0], ![-2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {2} * I13N1 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E13RS1 


noncomputable def E19RS0 : RelationCertificate Table 24 ![![19, 0, 0], ![0, 1, 0]]
  ![-76, -5, 1] ![![24, 0, 0], ![-437, -32, 7]] where
    su := ![![456, 0, 0], ![0, 24, 0]]
    hsu := by decide
    w := ![![-1824, -120, 24], ![7752, 912, -144]]
    hw := by decide
    g := ![![![133, -782, -255], ![3489, 572, 0]], ![![-4, -990, -316], ![4352, 715, 0]]]
    h := ![![![-4, 0, 0], ![-5, 1, 0]], ![![17, 2, -1], ![0, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {24} * I19N0 =  Ideal.span {B.equivFun.symm ![-76, -5, 1]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E19RS0 


noncomputable def E23RS1 : RelationCertificate Table 288 ![![23, 0, 0], ![-9, 1, 0]]
  ![-28, -11, 1] ![![288, 0, 0], ![-6773, -540, 107]] where
    su := ![![6624, 0, 0], ![-2592, 288, 0]]
    hsu := by decide
    w := ![![-8064, -3168, 288], ![-462816, -32832, 6336]]
    hw := by decide
    g := ![![![7109184, 17609963, 11497489], ![-195819585, -32669294, 0]], ![![-2458766, -6105158, -3986452], ![67893911, 11326945, 0]]]
    h := ![![![-82352, 10221, -119], ![-210452, 2738, 0]], ![![-4766626, 590929, -6812], ![-12181199, 156698, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {288} * I23N1 =  Ideal.span {B.equivFun.symm ![-28, -11, 1]} * (J0 ^ 7*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_2 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 64 ![![29, 0, 0], ![7, 1, 0]]
  ![28, 11, 1] ![![64, 0, 0], ![-1811, -148, 29]] where
    su := ![![1856, 0, 0], ![448, 64, 0]]
    hsu := by decide
    w := ![![1792, 704, 64], ![14272, 3200, 128]]
    hw := by decide
    g := ![![![27072, 107943, 68891], ![-947469, -155862, 0]], ![![7646, 28316, 18034], ![-248127, -40821, 0]]]
    h := ![![![7672, 1194, 14], ![-31780, -405, 0]], ![![60885, 9475, 111], ![-252206, -3217, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {64} * I29N0 =  Ideal.span {B.equivFun.symm ![28, 11, 1]} * (J0 ^ 11*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_0 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 288 ![![29, 0, 0], ![-4, 1, 0]]
  ![-116, -25, -1] ![![288, 0, 0], ![-6773, -540, 107]] where
    su := ![![8352, 0, 0], ![-1152, 288, 0]]
    hsu := by decide
    w := ![![-33408, -7200, -288], ![-25632, -11520, -2304]]
    hw := by decide
    g := ![![![-6243207515, -15475246900, -10104033107], ![172085948699, 28709694400, 0]], ![![968716750, 2401178144, 1567766782], ![-26701282844, -4454667465, 0]]]
    h := ![![![-141964, 36113, -156], ![-1029210, 4523, 0]], ![![-108697, 27651, -120], ![-788031, 3472, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {288} * I29N1 =  Ideal.span {B.equivFun.symm ![-116, -25, -1]} * (J0 ^ 7*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_2 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 48 ![![29, 0, 0], ![-3, 1, 0]]
  ![-52, -5, 1] ![![48, 0, 0], ![-181, -20, 3]] where
    su := ![![1392, 0, 0], ![-144, 48, 0]]
    hsu := by decide
    w := ![![-2496, -240, 48], ![-3888, -240, 48]]
    hw := by decide
    g := ![![![240, -34, -7], ![-769, -132, 0]], ![![18, 8, 0], ![87, 13, 0]]]
    h := ![![![-62, 23, -1], ![-582, 30, 0]], ![![-93, 33, -1], ![-872, 30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {48} * I29N2 =  Ideal.span {B.equivFun.symm ![-52, -5, 1]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E29RS2 
