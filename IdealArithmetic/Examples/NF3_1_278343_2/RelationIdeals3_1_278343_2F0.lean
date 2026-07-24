import IdealArithmetic.Examples.NF3_1_278343_2.PrimesBelow3_1_278343_2F0
import IdealArithmetic.Examples.NF3_1_278343_2.ClassGroupData3_1_278343_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![82, -12, -1], ![-6, 0, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![82, -12, -1], ![-6, 0, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![10, 0, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![10, 0, 1]] where
    su := ![![2, 0, 0], ![10, 0, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![10, 0, 1]]
    hw := by decide
    g := ![![![2, -5, -9], ![16, -2, 0]], ![![15, -25, -44], ![79, -10, 0]]]
    h := ![![![2, -5, -9], ![16, -2, 0]], ![![15, -25, -44], ![79, -10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 4 ![![2, 0, 0], ![10, 1, 1]]
  ![24121496, 972339, 1369575] ![![4, 0, 0], ![9, 1, 1]] where
    su := ![![8, 0, 0], ![40, 4, 4]]
    hsu := by decide
    w := ![![96485984, 3889356, 5478300], ![375863376, 15151076, 21340844]]
    hw := by decide
    g := ![![![91, -228, 126], ![189, 0, 0]], ![![56, 364, -890], ![-17, 0, 0]]]
    h := ![![![373317591, -1001818549, -72942335], ![1329207549, -168850472, 0]], ![![1454267309, -3902607261, -284148546], ![5177958659, -657760908, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {4} * I2N2 =  Ideal.span {B.equivFun.symm ![24121496, 972339, 1369575]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E2RS2 


noncomputable def E3RS0 : RelationCertificate Table 2 ![![3, 0, 0], ![1, 1, 0]]
  ![166807, 6724, 9471] ![![2, 0, 0], ![10, 0, 1]] where
    su := ![![6, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![333614, 13448, 18942], ![1985410, 80032, 112728]]
    hw := by decide
    g := ![![![86, -110, -216], ![347, -44, 0]], ![![-10, 88, 3], ![-17, -11, 0]]]
    h := ![![![55509, 2148, 28413], ![19222, -9471, 0]], ![![330351, 12788, 169092], ![114380, -56364, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![166807, 6724, 9471]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 4 ![![5, 0, 0], ![8, 2, 1]]
  ![1, -1, 2] ![![4, 0, 0], ![-9, 1, -1]] where
    su := ![![20, 0, 0], ![32, 8, 4]]
    hsu := by decide
    w := ![![4, -4, 8], ![280, -60, 0]]
    hw := by decide
    g := ![![![-309, 338, 94], ![759, 0, 78]], ![![-446, 516, 139], ![1114, 0, 117]]]
    h := ![![![-3, -1, 0], ![2, 0, 0]], ![![-2, -7, -2], ![10, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {4} * I5N0 =  Ideal.span {B.equivFun.symm ![1, -1, 2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 4 ![![5, 0, 0], ![0, 1, 0]]
  ![1433, 1126, -3523] ![![4, 0, 0], ![11, -1, 1]] where
    su := ![![20, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![5732, 4504, -14092], ![474632, -102184, 1868]]
    hw := by decide
    g := ![![![59068880, 55093305, -10356947], ![146076887, 0, 0]], ![![55284403, 51563522, -9693412], ![136717898, -7, 0]]]
    h := ![![![277, -9488, -743], ![48542, 24, 0]], ![![-830606, -415652, -3417257], ![-83130, 2135844, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {4} * I5N1 =  Ideal.span {B.equivFun.symm ![1433, 1126, -3523]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![8, 2, 1]]
  ![34309, 1383, 1948] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![16, 4, 2]]
    hsu := by decide
    w := ![![68618, 2766, 3896], ![160554, 6472, 9116]]
    hw := by decide
    g := ![![![8785, -1302, -109], ![-651, 0, -216]], ![![9773, -1444, -131], ![-720, 0, -243]]]
    h := ![![![2195, -479, -60], ![2368, 0, 0]], ![![5139, -1120, -140], ![5538, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![34309, 1383, 1948]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 4 ![![7, 0, 0], ![-1, 1, 0]]
  ![2686947, 108311, 152560] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![28, 0, 0], ![-4, 4, 0]]
    hsu := by decide
    w := ![![10747788, 433244, 610240], ![17947876, 723480, 1019048]]
    hw := by decide
    g := ![![![33695, -11051, 445], ![14085, 0, -1998]], ![![-568, 213, -27], ![-226, 0, 0]]]
    h := ![![![112515079, 2265465, 457546680], ![-15749944, -400334275, 0]], ![![187890447, 3783130, 764063366], ![-26301040, -668523600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {4} * I7N1 =  Ideal.span {B.equivFun.symm ![2686947, 108311, 152560]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 4 ![![13, 0, 0], ![0, 1, 0]]
  ![61027, 2460, 3465] ![![4, 0, 0], ![12, 0, 1]] where
    su := ![![52, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![244108, 9840, 13860], ![848424, 34200, 48172]]
    hw := by decide
    g := ![![![7549, -2634, -6172], ![21141, -3502, 0]], ![![4085693616, -1420727141, -3329737354], ![11424646524, -1894302877, 0]]]
    h := ![![![-427189, -214484, -1727267], ![-16490, 2807242, 0]], ![![-1484742, -745461, -6003305], ![-57333, 9756876, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {4} * I13N0 =  Ideal.span {B.equivFun.symm ![61027, 2460, 3465]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E13RS0 


noncomputable def E17RS0 : RelationCertificate Table 2 ![![17, 0, 0], ![5, 1, 0]]
  ![2520140, 101587, 143089] ![![2, 0, 0], ![11, 1, 1]] where
    su := ![![34, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![5040280, 203174, 286178], ![44309334, 1786112, 2515804]]
    hw := by decide
    g := ![![![44, -358, 132], ![157, 0, 0]], ![![82, -336, -187], ![210, 0, 0]]]
    h := ![![![-57509431, -196411396, -264114207], ![-28468137, 561260576, 0]], ![![-505568030, -1726661637, -2321840178], ![-250264811, 4934067616, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {2} * I17N0 =  Ideal.span {B.equivFun.symm ![2520140, 101587, 143089]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![-3, 1, 0]]
  ![-3, 1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![68, 0, 0], ![-12, 4, 0]]
    hsu := by decide
    w := ![![-12, 4, 0], ![-4, 0, 8]]
    hw := by decide
    g := ![![![-299585, 98372, -4471], ![-125197, 0, 17886]], ![![36313, -11925, 542], ![15180, 0, -2168]]]
    h := ![![![-240, 248, -1008], ![69, 2142, 0]], ![![-77, 80, -326], ![26, 693, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![-3, 1, 0]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 4 ![![17, 0, 0], ![-2, 1, 0]]
  ![299, 12, 17] ![![4, 0, 0], ![12, 0, 1]] where
    su := ![![68, 0, 0], ![-8, 4, 0]]
    hsu := by decide
    w := ![![1196, 48, 68], ![4152, 168, 236]]
    hw := by decide
    g := ![![![112430188, -39095595, -91627775], ![314383637, -52127462, 0]], ![![-14053777, 4886948, 11453469], ![-39297942, 6515931, 0]]]
    h := ![![![-111, 65, -527], ![29, 1122, 0]], ![![-390, 228, -1829], ![60, 3894, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {4} * I17N2 =  Ideal.span {B.equivFun.symm ![299, 12, 17]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E17RS2 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![9, 1, 0]]
  ![142208836, 5732447, 8074361] ![![2, 0, 0], ![11, 1, 1]] where
    su := ![![38, 0, 0], ![18, 2, 0]]
    hsu := by decide
    w := ![![284417672, 11464894, 16148722], ![2500328874, 100788412, 141964160]]
    hw := by decide
    g := ![![![-986, 4230, 1624], ![-2491, 0, 0]], ![![-409, 919, 1836], ![-840, 0, 0]]]
    h := ![![![6182793361, 42886205906, 34527500339], ![5185860333, -82001804010, 0]], ![![54353221661, 377014614352, 303532848144], ![45589137338, -720881641582, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![142208836, 5732447, 8074361]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 4 ![![19, 0, 0], ![-8, 1, 0]]
  ![-211, 52, -17] ![![4, 0, 0], ![12, 0, 1]] where
    su := ![![76, 0, 0], ![-32, 4, 0]]
    hsu := by decide
    w := ![![-844, 208, -68], ![2088, -360, -212]]
    hw := by decide
    g := ![![![-3171, 3110, 4296], ![-8429, 2718, 0]], ![![7882993, -2741522, -6424742], ![22042800, -3655113, 0]]]
    h := ![![![-1143, 5033, -5795], ![752, 13761, 0]], ![![2806, -12323, 14185], ![-1825, -33696, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {4} * I19N1 =  Ideal.span {B.equivFun.symm ![-211, 52, -17]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 4 ![![19, 0, 0], ![-1, 1, 0]]
  ![-18035, -727, -1024] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![76, 0, 0], ![-4, 4, 0]]
    hsu := by decide
    w := ![![-72140, -2908, -4096], ![-120468, -4856, -6840]]
    hw := by decide
    g := ![![![-213150, 69991, -3190], ![-89073, 0, 12726]], ![![-32, 10, 1], ![-10, 0, 0]]]
    h := ![![![-2279022, -6334, -9137528], ![119619, 21701501, 0]], ![![-3805784, -10577, -15258938], ![199749, 36239764, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {4} * I19N2 =  Ideal.span {B.equivFun.symm ![-18035, -727, -1024]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS2 


noncomputable def E31RS1 : RelationCertificate Table 4 ![![31, 0, 0], ![12, 1, 0]]
  ![363, -67, -26] ![![4, 0, 0], ![-9, 1, -1]] where
    su := ![![124, 0, 0], ![48, 4, 0]]
    hsu := by decide
    w := ![![1452, -268, -104], ![-704, 596, -1096]]
    hw := by decide
    g := ![![![-28639, -6580, 6332], ![61211, 0, 1976]], ![![-15100, -3863, 3316], ![32195, 0, 988]]]
    h := ![![![-2955, -24025, -14822], ![-1908, 57432, 0]], ![![1492, 12236, 7538], ![1005, -29244, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4} * I31N1 =  Ideal.span {B.equivFun.symm ![363, -67, -26]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS1 
