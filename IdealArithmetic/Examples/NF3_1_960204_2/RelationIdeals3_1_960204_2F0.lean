import IdealArithmetic.Examples.NF3_1_960204_2.PrimesBelow3_1_960204_2F0
import IdealArithmetic.Examples.NF3_1_960204_2.ClassGroupData3_1_960204_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 121 ![![2, 0, 0], ![0, 1, 0]]
  ![-8, 13, -6] ![![121, 0, 0], ![-55, 1, 0]] where
    su := ![![242, 0, 0], ![0, 121, 0]]
    hsu := by decide
    w := ![![-968, 1573, -726], ![121, -484, 363]]
    hw := by decide
    g := ![![![-49211, -2747859, 147207], ![-324, -5937344, 0]], ![![-6018, -338407, 18129], ![48, -731200, 0]]]
    h := ![![![0, 8, -15], ![5, 8, 0]], ![![0, -2, 3], ![-1, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {121} * I2N0 =  Ideal.span {B.equivFun.symm ![-8, 13, -6]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![29, 0, 1]]
  ![1, 0, 0] ![![3, 0, 0], ![29, 0, 1]] where
    su := ![![3, 0, 0], ![29, 0, 1]]
    hsu := by decide
    w := ![![3, 0, 0], ![29, 0, 1]]
    hw := by decide
    g := ![![![-28, 0, -1], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-28, 0, -1], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![-29, -1, -1]]
  ![42, 0, 1] ![![3, 0, 0], ![29, 0, 1]] where
    su := ![![9, 0, 0], ![-87, -3, -3]]
    hsu := by decide
    w := ![![126, 0, 3], ![1266, 3, 30]]
    hw := by decide
    g := ![![![-2940, 2420, -11135], ![4318, -1, -2424]], ![![-1617, 1331, -5907], ![2278, 10, -1286]]]
    h := ![![![85, -1171, -396], ![-276, 0, 83]], ![![857, -11766, -3979], ![-2773, 0, 834]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![42, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS1 


noncomputable def E11RS0 : RelationCertificate Table 1 ![![11, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![0, 1, 0]] where
    su := ![![11, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 3], ![0, -11, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 3], ![0, -11, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {1} * I11N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 121 ![![11, 0, 0], ![27, -4, 1]]
  ![-10246, -18, -243] ![![121, 0, 0], ![-55, 1, 0]] where
    su := ![![1331, 0, 0], ![3267, -484, 121]]
    hsu := by decide
    w := ![![-1239766, -2178, -29403], ![551155, 968, 13068]]
    hw := by decide
    g := ![![![-160, -9184, 492], ![9, -19844, 0]], ![![-407, -23055, 1235], ![10, -49815, 0]]]
    h := ![![![-173, -114, 6], ![-309, 0, 0]], ![![41, 56, -4], ![152, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {121} * I11N1 =  Ideal.span {B.equivFun.symm ![-10246, -18, -243]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 363 ![![13, 0, 0], ![23, 3, 1]]
  ![-279, 45, 184] ![![363, 0, 0], ![62, 0, 1]] where
    su := ![![4719, 0, 0], ![8349, 1089, 363]]
    hsu := by decide
    w := ![![-101277, 16335, 66792], ![-6171, 1452, 3630]]
    hw := by decide
    g := ![![![146220933736, 59014856994, 2881921050], ![24982313607, -1071119654440, 0]], ![![257350657837, 103866880629, 5072216810], ![43969182063, -1885183883414, 0]]]
    h := ![![![-25, 3, 14], ![2, 0, 0]], ![![-19, -2, 0], ![10, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {363} * I13N0 =  Ideal.span {B.equivFun.symm ![-279, 45, 184]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 99 ![![13, 0, 0], ![3, 1, 0]]
  ![-21, -3, 20] ![![99, 0, 0], ![62, 0, 1]] where
    su := ![![1287, 0, 0], ![297, 99, 0]]
    hsu := by decide
    w := ![![-2079, -297, 1980], ![-495, 0, 396]]
    hw := by decide
    g := ![![![-4006335, -2187488, -84024], ![-2509862, 10828065, 0]], ![![-9568013, -5224236, -200667], ![-5993991, 25859968, 0]]]
    h := ![![![81, -173, -256], ![14, 1116, 0]], ![![19, -42, -62], ![6, 270, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {99} * I13N1 =  Ideal.span {B.equivFun.symm ![-21, -3, 20]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![-7, 1, 0]]
  ![-6, 6, -1] ![![3, 0, 0], ![29, 0, 1]] where
    su := ![![51, 0, 0], ![-21, 3, 0]]
    hsu := by decide
    w := ![![-18, 18, -3], ![84, -81, 12]]
    hw := by decide
    g := ![![![-10, 1, -7], ![65, 0, 0]], ![![-15, 4, 2], ![-22, 1, 0]]]
    h := ![![![226, 1724, -647], ![26, 3666, 0]], ![![-1018, -8028, 3011], ![-39, -17061, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![-6, 6, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 121 ![![19, 0, 0], ![4, 1, 0]]
  ![-38402, -63, -911] ![![121, 0, 0], ![-55, 1, 0]] where
    su := ![![2299, 0, 0], ![484, 121, 0]]
    hsu := by decide
    w := ![![-4646642, -7623, -110231], ![2065712, 3388, 49005]]
    hw := by decide
    g := ![![![-2782955, -155364246, 8323093], ![-18901, -335698082, 0]], ![![-806975, -45051770, 2413490], ![-5453, -97344100, 0]]]
    h := ![![![22907906, -69525848, -69464657], ![1163477, 439942524, 0]], ![![-10183948, 30908425, 30881223], ![-517215, -195580944, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {121} * I19N1 =  Ideal.span {B.equivFun.symm ![-38402, -63, -911]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 33 ![![23, 0, 0], ![2, 1, 0]]
  ![-1277202, -2103, -30299] ![![33, 0, 0], ![29, 0, 1]] where
    su := ![![759, 0, 0], ![66, 33, 0]]
    hsu := by decide
    w := ![![-42147666, -69399, -999867], ![-38600463, -63558, -915717]]
    hw := by decide
    g := ![![![-325, 143, 0], ![-247, 342, 0]], ![![-18319829, 8277063, -148705], ![-16103707, 21011020, 0]]]
    h := ![![![499107004, -501976828, -1503117325], ![21575549, 11523889392, 0]], ![![457101503, -459729798, -1376612995], ![19759716, 10554023712, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {33} * I23N0 =  Ideal.span {B.equivFun.symm ![-1277202, -2103, -30299]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 33 ![![23, 0, 0], ![-4, 1, 0]]
  ![-1111413, -1830, -26366] ![![33, 0, 0], ![29, 0, 1]] where
    su := ![![759, 0, 0], ![-132, 33, 0]]
    hsu := by decide
    w := ![![-36676629, -60390, -870078], ![-33589875, -55308, -796851]]
    hw := by decide
    g := ![![![-498096744136023, 225044951819552, -4043153139890], ![-437843901002562, 571267954618894, 0]], ![![108281900706471, -48922815525898, 878946333193], ![95183456570338, -124188685565755, 0]]]
    h := ![![![1607931, 8210553, -4929544], ![77361, 37784382, 0]], ![![1472605, 7519542, -4514667], ![70848, 34604398, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {33} * I23N1 =  Ideal.span {B.equivFun.symm ![-1111413, -1830, -26366]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 363 ![![29, 0, 0], ![11, 1, 0]]
  ![163854, 270, 3887] ![![363, 0, 0], ![62, 0, 1]] where
    su := ![![10527, 0, 0], ![3993, 363, 0]]
    hsu := by decide
    w := ![![59479002, 98010, 1410981], ![10359294, 17061, 245751]]
    hw := by decide
    g := ![![![5093993270047834, 2055938754646493, 100399348146829], ![870325019534886, -37315288396833853, 0]], ![![1756549415354705, 708944402952763, 34620465112560], ![300112077733340, -12867340913592647, 0]]]
    h := ![![![-469937528, 4754218298, 1426117549], ![-14313592, -13785801678, 0]], ![![-81847737, 828029201, 248382994], ![-2492952, -2401035383, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {363} * I29N1 =  Ideal.span {B.equivFun.symm ![163854, 270, 3887]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 11 ![![31, 0, 0], ![8, 1, 0]]
  ![-369, 271, 34] ![![11, 0, 0], ![0, 1, 0]] where
    su := ![![341, 0, 0], ![88, 11, 0]]
    hsu := by decide
    w := ![![-4059, 2981, 374], ![1463, -2068, 847]]
    hw := by decide
    g := ![![![-104532, -243, -2261], ![-15, -796, 0]], ![![-31049, -71, -675], ![-5, -224, 0]]]
    h := ![![![18268, -129006, -55283], ![574, 571269, 0]], ![![-7533, 53165, 22787], ![-223, -235440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {11} * I31N1 =  Ideal.span {B.equivFun.symm ![-369, 271, 34]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS1 
