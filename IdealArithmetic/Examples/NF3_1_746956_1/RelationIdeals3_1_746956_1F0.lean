import IdealArithmetic.Examples.NF3_1_746956_1.PrimesBelow3_1_746956_1F0
import IdealArithmetic.Examples.NF3_1_746956_1.ClassGroupData3_1_746956_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 891 ![![2, 0, 0], ![0, 1, 0]]
  ![52, -9, -22] ![![891, 0, 0], ![-41, 1, 0]] where
    su := ![![1782, 0, 0], ![0, 891, 0]]
    hsu := by decide
    w := ![![46332, -8019, -19602], ![-4455, 891, 891]]
    hw := by decide
    g := ![![![-789, -30926, 9190], ![833, -744667, -68]], ![![-477, -18185, 5404], ![194, -437885, -40]]]
    h := ![![![0, 79, 275], ![41, -52, 0]], ![![0, -8, -27], ![-3, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {891} * I2N0 =  Ideal.span {B.equivFun.symm ![52, -9, -22]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 243 ![![3, 0, 0], ![14, 0, 1]]
  ![86, -18, 1] ![![243, 0, 0], ![-41, 1, 0]] where
    su := ![![729, 0, 0], ![3402, 0, 243]]
    hsu := by decide
    w := ![![20898, -4374, 243], ![-3402, 729, -243]]
    hw := by decide
    g := ![![![77, 2425, -721], ![65, 15928, 0]], ![![336, 11315, -3364], ![165, 74316, 0]]]
    h := ![![![-4, -6, -2], ![7, 0, 0]], ![![-14, 1, -1], ![2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {243} * I3N0 =  Ideal.span {B.equivFun.symm ![86, -18, 1]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 11 ![![7, 0, 0], ![0, 1, 0]]
  ![-7, 1, 0] ![![11, 0, 0], ![3, 1, 0]] where
    su := ![![77, 0, 0], ![0, 11, 0]]
    hsu := by decide
    w := ![![-77, 11, 0], ![-22, 0, 11]]
    hw := by decide
    g := ![![![-289707, 73712, 2919], ![-72303, 0, 32110]], ![![-38123, 9698, 384], ![-9504, 0, 4225]]]
    h := ![![![0, -4, -11], ![1, 7, 0]], ![![0, -2, -3], ![6, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {11} * I7N0 =  Ideal.span {B.equivFun.symm ![-7, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 1 ![![11, 0, 0], ![3, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![3, 1, 0]] where
    su := ![![11, 0, 0], ![3, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![3, 1, 0]]
    hw := by decide
    g := ![![![1189, -304, -12], ![308, 0, -132]], ![![297, -76, -3], ![78, 0, -33]]]
    h := ![![![1189, -304, -12], ![308, 0, -132]], ![![297, -76, -3], ![78, 0, -33]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {1} * I11N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 121 ![![11, 0, 0], ![4, 1, 0]]
  ![2302, 75, 99] ![![121, 0, 0], ![36, 1, 0]] where
    su := ![![1331, 0, 0], ![484, 121, 0]]
    hsu := by decide
    w := ![![278542, 9075, 11979], ![93291, 3025, 3993]]
    hw := by decide
    g := ![![![-209757835, 8315135553, 2286676656], ![6312933, -25153442928, -99]], ![![-76275717, 3023690495, 831520115], ![2295678, -9146721160, -36]]]
    h := ![![![182, 0, 9], ![75, 0, 0]], ![![61, 0, 3], ![25, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {121} * I11N1 =  Ideal.span {B.equivFun.symm ![2302, 75, 99]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 363 ![![13, 0, 0], ![11, 4, 1]]
  ![4, -21, 11] ![![363, 0, 0], ![157, 1, 0]] where
    su := ![![4719, 0, 0], ![3993, 1452, 363]]
    hsu := by decide
    w := ![![1452, -7623, 3993], ![1815, -3630, 1452]]
    hw := by decide
    g := ![![![-639144189414883, 102490712399236333, 7002472144174586], ![5909296587120, -231081580808296960, 3633280]], ![![-556968507885604, 89313335085444793, 6102154296703063], ![5149529882953, -201371091835239264, 3166144]]]
    h := ![![![-9, -5, 0], ![11, 0, 0]], ![![-3, -2, 0], ![4, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {363} * I13N0 =  Ideal.span {B.equivFun.symm ![4, -21, 11]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 2673 ![![13, 0, 0], ![-1, 1, 0]]
  ![1762, 72, 77] ![![2673, 0, 0], ![-41, 1, 0]] where
    su := ![![34749, 0, 0], ![-2673, 2673, 0]]
    hsu := by decide
    w := ![![4709826, 192456, 205821], ![-64152, -2673, -2673]]
    hw := by decide
    g := ![![![1067672859, 39526234993, -11750760973], ![-1588545, 2855494337074, 14525044]], ![![112386635, 4160656144, -1236922157], ![-165725, 300578338954, 1528952]]]
    h := ![![![9633, -28943, -106975], ![-2965, 126432, 0]], ![![-131, 394, 1457], ![43, -1722, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {2673} * I13N1 =  Ideal.span {B.equivFun.symm ![1762, 72, 77]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 81 ![![17, 0, 0], ![-5, 1, 0]]
  ![308, 9, 13] ![![81, 0, 0], ![40, 1, 0]] where
    su := ![![1377, 0, 0], ![-405, 81, 0]]
    hsu := by decide
    w := ![![24948, 729, 1053], ![13689, 405, 567]]
    hw := by decide
    g := ![![![-407129, 17568276, 4392118], ![15887, -32341960, 0]], ![![42110, -1817408, -454357], ![-1630, 3345720, 0]]]
    h := ![![![-317, -366, 3975], ![89, -6142, 0]], ![![-173, -201, 2181], ![52, -3370, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {81} * I17N1 =  Ideal.span {B.equivFun.symm ![308, 9, 13]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 33 ![![19, 0, 0], ![-8, 1, 0]]
  ![256, 9, 11] ![![33, 0, 0], ![-8, 1, 0]] where
    su := ![![627, 0, 0], ![-264, 33, 0]]
    hsu := by decide
    w := ![![8448, 297, 363], ![-891, -33, -33]]
    hw := by decide
    g := ![![![-1843406, 8454363, -20525173], ![703087, 62906881, 1220415]], ![![760278, -3486828, 8465184], ![-289962, -25944645, -503335]]]
    h := ![![![-53881, -233651, 641036], ![10406, -1107243, 0]], ![![5683, 24636, -67591], ![-1093, 116748, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {33} * I19N1 =  Ideal.span {B.equivFun.symm ![256, 9, 11]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 3267 ![![23, 0, 0], ![6, 1, 0]]
  ![-458, 45, 11] ![![3267, 0, 0], ![-932, 1, 0]] where
    su := ![![75141, 0, 0], ![19602, 3267, 0]]
    hsu := by decide
    w := ![![-1496286, 147015, 35937], ![427977, -42471, -9801]]
    hw := by decide
    g := ![![![458341251931, 425483636328050, -5043391423364], ![-517419439, 1497904132331660, 198371280]], ![![139412130780, 129417939383125, -1534031557940], ![-157381801, 455612506917581, 60337931]]]
    h := ![![![403, -4076, -4488], ![-57, 9385, 0]], ![![-122, 1165, 1284], ![42, -2685, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {3267} * I23N1 =  Ideal.span {B.equivFun.symm ![-458, 45, 11]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 363 ![![29, 0, 0], ![-12, 1, 0]]
  ![136, 12, 11] ![![363, 0, 0], ![157, 1, 0]] where
    su := ![![10527, 0, 0], ![-4356, 363, 0]]
    hsu := by decide
    w := ![![49368, 4356, 3993], ![22506, 1815, 1815]]
    hw := by decide
    g := ![![![-46232799, 7527747154, 515550954], ![741697, -16972916402, -2894875]], ![![18493035, -3011098868, -206220382], ![-296483, 6789166574, 1157950]]]
    h := ![![![-559048, -4703736, 6464359], ![69156, -17042400, 0]], ![![-255018, -2145717, 2948865], ![31558, -7774280, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {363} * I29N1 =  Ideal.span {B.equivFun.symm ![136, 12, 11]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E29RS1 
