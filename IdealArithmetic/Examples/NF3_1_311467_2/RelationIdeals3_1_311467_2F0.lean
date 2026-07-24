import IdealArithmetic.Examples.NF3_1_311467_2.PrimesBelow3_1_311467_2F0
import IdealArithmetic.Examples.NF3_1_311467_2.ClassGroupData3_1_311467_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 4 ![![2, 0, 0], ![-29, 3, 1]]
  ![2389409, 235539, -10467] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![8, 0, 0], ![-116, 12, 4]]
    hsu := by decide
    w := ![![9557636, 942156, -41868], ![1758456, 1939328, 225072]]
    hw := by decide
    g := ![![![-50732309108, 18514911805, -2291005640], ![4628727953, 62, 0]], ![![-147059506735, 53669818015, -6641017371], ![13417454507, -868, 0]]]
    h := ![![![31384, 238113, 34881], ![-80229, 0, 0]], ![![29248, 262129, 34705], ![-13142, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {4} * I2N1 =  Ideal.span {B.equivFun.symm ![2389409, 235539, -10467]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 2 ![![3, 0, 0], ![0, 1, 0]]
  ![-111, 43, -5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![6, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![-222, 86, -10], ![840, -326, 38]]
    hw := by decide
    g := ![![![31, -3, -1], ![-1, 0, 0]], ![![56, -4, 0], ![0, -3, 0]]]
    h := ![![![-37, 12, 0], ![7, -5, 0]], ![![140, -49, 0], ![-16, 19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![-111, 43, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 4 ![![3, 0, 0], ![-31, 2, 1]]
  ![-16251952951, 6301900079, -733917227] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![12, 0, 0], ![-124, 8, 4]]
    hsu := by decide
    w := ![![-65007811804, 25207600316, -2935668908], ![123298094136, -47810393712, 5567982852]]
    hw := by decide
    g := ![![![115863, -10720, -25998775996174], ![-2678, 103995103970639, 0]], ![![30955, 72818, 285986535928906], ![18205, -1143946143676983, 0]]]
    h := ![![![48013360, 1748031359, -420940076], ![528903001, 0, 0]], ![![-91065240, -3315431320, 798382649], ![-1003152234, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {4} * I3N1 =  Ideal.span {B.equivFun.symm ![-16251952951, 6301900079, -733917227]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![-29, 6, 1]]
  ![-1022891, 158177, 38621] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![-58, 12, 2]]
    hsu := by decide
    w := ![![-2045782, 316354, 77242], ![-6488328, 637812, 196798]]
    hw := by decide
    g := ![![![-5137420589, 1593679790, -231999299], ![796839896, 27, 0]], ![![12449085835, -3861832249, 562184722], ![-1930916123, -135, 0]]]
    h := ![![![-9123, -5749, 793], ![33070, 0, 0]], ![![-33991, -43296, -752], ![103663, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-1022891, 158177, 38621]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 4 ![![7, 0, 0], ![0, 1, 0]]
  ![35, -3, -1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![28, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![140, -12, -4], ![168, -8, -4]]
    hw := by decide
    g := ![![![5, -2, 4], ![0, -15, 0]], ![![-6, 2, -4], ![1, 15, 0]]]
    h := ![![![5, 0, 0], ![-3, -1, 0]], ![![6, 0, 0], ![-2, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {4} * I7N1 =  Ideal.span {B.equivFun.symm ![35, -3, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0], ![1, 1, 0]]
  ![-13675, 1437, 427] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![22, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-27350, 2874, 854], ![-71736, 4686, 1864]]
    hw := by decide
    g := ![![![-3751469, 1163743, -169863], ![581873, 903, 0]], ![![2246333, -696836, 101377], ![-348416, 129, 0]]]
    h := ![![![-2446, -1084, 27], ![13231, 130, 0]], ![![-6416, -2972, 55], ![34708, 327, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![-13675, 1437, 427]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![2, 1, 0]]
  ![1295099, -502191, 58485] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![22, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![2590198, -1004382, 116970], ![-9825480, 3809954, -443706]]
    hw := by decide
    g := ![![![-4259, -213, 211], ![-105, -344, 0]], ![![-1370, -227, 51], ![-112, -129, 0]]]
    h := ![![![3302983, 1611874, 37769], ![-17518857, -356974, 0]], ![![-12529316, -6114379, -143272], ![66454868, 1354139, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![1295099, -502191, 58485]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 2 ![![11, 0, 0], ![-4, 1, 0]]
  ![-1949795, 249293, 66735] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![22, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![-3899590, 498586, 133470], ![-11211480, 919810, 316028]]
    hw := by decide
    g := ![![![96327197627, -29881670279, 4350011684], ![-14940835139, 559, 0]], ![![-101464618216, 31475350069, -4582011163], ![15737675035, -172, 0]]]
    h := ![![![-3264109, 853580, -8734], ![-8488851, 162809, 0]], ![![-9369556, 2429623, -28842], ![-24364844, 475276, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {2} * I11N2 =  Ideal.span {B.equivFun.symm ![-1949795, 249293, 66735]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 2 ![![13, 0, 0], ![4, 1, 0]]
  ![-10607, 4113, -479] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![26, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![-21214, 8226, -958], ![80472, -31204, 3634]]
    hw := by decide
    g := ![![![-731, 35, -1], ![18, 39, 0]], ![![-464, 14, 6], ![9, 9, 0]]]
    h := ![![![-42223, -11680, -448], ![134573, 5345, 0]], ![![160140, 44282, 1695], ![-510396, -20218, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {2} * I13N0 =  Ideal.span {B.equivFun.symm ![-10607, 4113, -479]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![-8, 1, 0]]
  ![25, -9, 1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![68, 0, 0], ![-32, 4, 0]]
    hsu := by decide
    w := ![![100, -36, 4], ![-168, 68, -8]]
    hw := by decide
    g := ![![![-1, 1, -3], ![3, 13, 0]], ![![-2, -1, 1], ![3, -4, 0]]]
    h := ![![![873, -125, 2], ![1852, -33, 0]], ![![-1434, 211, -4], ![-3042, 66, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![25, -9, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 4 ![![19, 0, 0], ![1, 1, 0]]
  ![2749, -237, -79] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![76, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![10996, -948, -316], ![13272, -648, -316]]
    hw := by decide
    g := ![![![-32801, 11970, -1467], ![2996, -57, 0]], ![![11371, -4150, 514], ![-1037, -2, 0]]]
    h := ![![![286, 129, -4], ![-2685, -3, 0]], ![![346, 163, -4], ![-3256, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {4} * I19N0 =  Ideal.span {B.equivFun.symm ![2749, -237, -79]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 4 ![![19, 0, 0], ![-3, 1, 0]]
  ![57351317663, -22238697983, 2589911511] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![76, 0, 0], ![-12, 4, 0]]
    hsu := by decide
    w := ![![229405270652, -88954791932, 10359646044], ![-435105133848, 168717512636, -19648786472]]
    hw := by decide
    g := ![![![200771, -94258, -15098], ![-23561, -6363, 0]], ![![115863, -10720, -3590], ![-2678, 303, 0]]]
    h := ![![![702220096907, -239333902276, 1835058572], ![4428276841190, -32276201357, 0]], ![![-1331876850012, 453936430001, -3480492856], ![-8398961288922, 61217167646, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {4} * I19N1 =  Ideal.span {B.equivFun.symm ![57351317663, -22238697983, 2589911511]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![-7, 1, 0]]
  ![95987, -67061, -10507] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![46, 0, 0], ![-14, 2, 0]]
    hsu := by decide
    w := ![![191974, -134122, -21014], ![1765176, -355814, -77568]]
    hw := by decide
    g := ![![![8100596521, -2512886914, 365813170], ![-1256443455, -1365, 0]], ![![-5137420589, 1593679790, -231999422], ![796839896, 273, 0]]]
    h := ![![![392299, -61651, 13], ![1275270, -10806, 0]], ![![3575278, -544845, 2862], ![11621258, -104610, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![95987, -67061, -10507]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 2 ![![29, 0, 0], ![3, 1, 0]]
  ![-34271639, 13289261, -1547663] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![58, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![-68543278, 26578522, -3095326], ![260007384, -100821148, 11741598]]
    hw := by decide
    g := ![![![40301, 1284, -532], ![644, 87, 0]], ![![6999, 665, -15], ![333, 6, 0]]]
    h := ![![![-34016857, -10616418, -96582], ![317405738, 1253215, 0]], ![![129037206, 40271579, 366364], ![-1204025094, -4753757, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {2} * I29N0 =  Ideal.span {B.equivFun.symm ![-34271639, 13289261, -1547663]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 2 ![![29, 0, 0], ![6, 1, 0]]
  ![4297729405, -1666498873, 194079915] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![58, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![8595458810, -3332997746, 388159830], ![-32605425720, 12643165750, -1472418958]]
    hw := by decide
    g := ![![![581597, -55379, -18999], ![-27689, -460, 0]], ![![231726, -18224, -6971], ![-9110, -115, 0]]]
    h := ![![![4255373015, 659756432, 12141189], ![-19851348005, -158014566, 0]], ![![-16142041056, -2502674953, -46055558], ![75302746294, 599401703, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2} * I29N1 =  Ideal.span {B.equivFun.symm ![4297729405, -1666498873, 194079915]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 2 ![![29, 0, 0], ![-10, 1, 0]]
  ![-893, 163, 37] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![58, 0, 0], ![-20, 2, 0]]
    hsu := by decide
    w := ![![-1786, 326, 74], ![-6216, 698, 200]]
    hw := by decide
    g := ![![![-37501, 11633, -4511], ![5817, 5635, 0]], ![![22742, -7055, 1947], ![-3527, -1840, 0]]]
    h := ![![![-1447, 160, 0], ![-4107, 37, 0]], ![![-5072, 543, 0], ![-14398, 100, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {2} * I29N2 =  Ideal.span {B.equivFun.symm ![-893, 163, 37]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS2 
