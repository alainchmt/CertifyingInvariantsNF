import IdealArithmetic.Examples.NF3_1_343980_3.PrimesBelow3_1_343980_3F0
import IdealArithmetic.Examples.NF3_1_343980_3.ClassGroupData3_1_343980_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 5 ![![2, 0, 0], ![0, 1, 0]]
  ![-38, -3, 1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![10, 0, 0], ![0, 5, 0]]
    hsu := by decide
    w := ![![-190, -15, 5], ![230, 10, -5]]
    hw := by decide
    g := ![![![8, 38, -19], ![10, 96, 0]], ![![15, 16, -4], ![-1, 24, 0]]]
    h := ![![![-19, -2, 0], ![1, 1, 0]], ![![23, 0, 0], ![2, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {5} * I2N0 =  Ideal.span {B.equivFun.symm ![-38, -3, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 605 ![![3, 0, 0], ![-1, 1, 0]]
  ![187, 62, 6] ![![605, 0, 0], ![-212, 1, 0]] where
    su := ![![1815, 0, 0], ![-605, 605, 0]]
    hsu := by decide
    w := ![![113135, 37510, 3630], ![-38720, -12705, -1210]]
    hw := by decide
    g := ![![![263661, 510967517, -2410230], ![752429, 1458189152, 0]], ![![-46719, -90804469, 428324], ![-133326, -259136024, 0]]]
    h := ![![![136, -60, 9], ![221, -21, 0]], ![![-46, 21, -4], ![-74, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {605} * I3N0 =  Ideal.span {B.equivFun.symm ![187, 62, 6]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![5, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -1], ![-4, 5, 0]]]
    h := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -1], ![-4, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![-1, 1, 0]]
  ![117, 47, 6] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![25, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![585, 235, 30], ![690, 275, 35]]
    hw := by decide
    g := ![![![-79, -1150, 595], ![-193, -2976, 0]], ![![5, 141, -74], ![27, 372, 0]]]
    h := ![![![52, -20, 2], ![143, -4, 0]], ![![62, -24, 2], ![172, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![117, 47, 6]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 55 ![![7, 0, 0], ![0, 1, 0]]
  ![847, 2, -14] ![![55, 0, 0], ![8, 1, 0]] where
    su := ![![385, 0, 0], ![0, 55, 0]]
    hsu := by decide
    w := ![![46585, 110, -770], ![4620, 275, -110]]
    hw := by decide
    g := ![![![17, -145, -18], ![45, 1056, 0]], ![![20, -81, -10], ![44, 624, 0]]]
    h := ![![![121, 0, -2], ![2, 0, 0]], ![![12, 0, 0], ![5, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {55} * I7N0 =  Ideal.span {B.equivFun.symm ![847, 2, -14]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 605 ![![11, 0, 0], ![0, 1, 0]]
  ![95579, 38244, 4872] ![![605, 0, 0], ![-212, 1, 0]] where
    su := ![![6655, 0, 0], ![0, 605, 0]]
    hsu := by decide
    w := ![![57825295, 23137620, 2947560], ![-19512460, -7807525, -994620]]
    hw := by decide
    g := ![![![129, 2976, -14], ![380, 8494, 0]], ![![208, 1487, -7], ![592, 4247, 0]]]
    h := ![![![8689, 3448, 0], ![316, 4872, 0]], ![![-2932, -1164, 0], ![-101, -1644, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {605} * I11N0 =  Ideal.span {B.equivFun.symm ![95579, 38244, 4872]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 5 ![![11, 0, 0], ![3, 1, 0]]
  ![255, 102, 13] ![![5, 0, 0], ![-26, -4, 1]] where
    su := ![![55, 0, 0], ![15, 5, 0]]
    hsu := by decide
    w := ![![1275, 510, 65], ![1070, 430, 55]]
    hw := by decide
    g := ![![![13, -8, 1], ![-14, 0, 0]], ![![19, 5, -1], ![4, 0, 0]]]
    h := ![![![249, 90, 3], ![-828, -20, 0]], ![![206, 73, 2], ![-684, -11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {5} * I11N1 =  Ideal.span {B.equivFun.symm ![255, 102, 13]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 1 ![![11, 0, 0], ![-3, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![11, 0, 0], ![-3, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![-3, 1, 0]]
    hw := by decide
    g := ![![![19, -6, 0], ![66, 0, 0]], ![![-3, 4, -1], ![-10, 11, 0]]]
    h := ![![![19, -6, 0], ![66, 0, 0]], ![![-3, 4, -1], ![-10, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {1} * I11N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 55 ![![13, 0, 0], ![2, 1, 0]]
  ![33, 8, -1] ![![55, 0, 0], ![8, 1, 0]] where
    su := ![![715, 0, 0], ![110, 55, 0]]
    hsu := by decide
    w := ![![1815, 440, -55], ![110, 55, 0]]
    hw := by decide
    g := ![![![-7, 103, 13], ![45, -714, 0]], ![![-8, 135, 17], ![56, -935, 0]]]
    h := ![![![3039, 1559, 20], ![-19737, -261, 0]], ![![182, 93, 1], ![-1182, -13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {55} * I13N0 =  Ideal.span {B.equivFun.symm ![33, 8, -1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 55 ![![13, 0, 0], ![-1, 1, 0]]
  ![6809, 2724, 347] ![![55, 0, 0], ![8, 1, 0]] where
    su := ![![715, 0, 0], ![-55, 55, 0]]
    hsu := by decide
    w := ![![374495, 149820, 19085], ![107910, 43175, 5500]]
    hw := by decide
    g := ![![![1, 1117, 140], ![39, -7695, 0]], ![![-7, -55, -7], ![52, 378, 0]]]
    h := ![![![1116, -386, 30], ![7699, -43, 0]], ![![322, -111, 8], ![2224, -4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {55} * I13N1 =  Ideal.span {B.equivFun.symm ![6809, 2724, 347]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 5 ![![19, 0, 0], ![-6, 1, 0]]
  ![17, 7, 1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![95, 0, 0], ![-30, 5, 0]]
    hsu := by decide
    w := ![![85, 35, 5], ![120, 45, 5]]
    hw := by decide
    g := ![![![1, -167, 87], ![-32, -437, 0]], ![![-2, 61, -32], ![14, 161, 0]]]
    h := ![![![539, -95, 1], ![1704, -18, 0]], ![![756, -131, 1], ![2390, -18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {5} * I19N1 =  Ideal.span {B.equivFun.symm ![17, 7, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 55 ![![23, 0, 0], ![5, 1, 0]]
  ![165, 26, -6] ![![55, 0, 0], ![-1, 1, 1]] where
    su := ![![1265, 0, 0], ![275, 55, 0]]
    hsu := by decide
    w := ![![9075, 1430, -330], ![2915, 55, -55]]
    hw := by decide
    g := ![![![-7595224, -2024417, -51157], ![100391, 2713230, 0]], ![![-1713795, -456793, -11544], ![22696, 612216, 0]]]
    h := ![![![33815, 7164, 80], ![-155516, -1846, 0]], ![![10821, 2294, 26], ![-49766, -599, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {55} * I23N0 =  Ideal.span {B.equivFun.symm ![165, 26, -6]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 121 ![![23, 0, 0], ![-3, 1, 0]]
  ![-5115, -361, 129] ![![121, 0, 0], ![30, 1, 0]] where
    su := ![![2783, 0, 0], ![-363, 121, 0]]
    hsu := by decide
    w := ![![-618915, -43681, 15609], ![-133584, -10527, 3509]]
    hw := by decide
    g := ![![![-111897, 58021348, 1934174], ![451811, -234034300, 0]], ![![10979, -5676894, -189241], ![-44178, 22898320, 0]]]
    h := ![![![-6435, 2087, -5], ![-47630, 244, 0]], ![![-1386, 449, -1], ![-10258, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {121} * I23N1 =  Ideal.span {B.equivFun.symm ![-5115, -361, 129]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 5 ![![23, 0, 0], ![-2, 1, 0]]
  ![-489, -79, 18] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![115, 0, 0], ![-10, 5, 0]]
    hsu := by decide
    w := ![![-2445, -395, 90], ![3750, 425, -115]]
    hw := by decide
    g := ![![![1021, 724, -53], ![-263, 552, 0]], ![![254, 102, 29], ![-81, -72, 0]]]
    h := ![![![-4799, 2403, -8], ![-54944, 202, 0]], ![![7370, -3689, 11], ![84380, -276, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {5} * I23N2 =  Ideal.span {B.equivFun.symm ![-489, -79, 18]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS2 


noncomputable def E29RS1 : RelationCertificate Table 605 ![![29, 0, 0], ![7, 1, 0]]
  ![-2497, -1000, -128] ![![605, 0, 0], ![219, 1, 1]] where
    su := ![![17545, 0, 0], ![4235, 605, 0]]
    hsu := by decide
    w := ![![-1510685, -605000, -77440], ![-720555, -288585, -36905]]
    hw := by decide
    g := ![![![-646, -1032, -4], ![93, 2391, 0]], ![![-151, -286, -1], ![-50, 663, 0]]]
    h := ![![![-6485988, -1009651, -11870], ![26870165, 344102, 0]], ![![-3093644, -481579, -5662], ![12816355, 164137, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {605} * I29N1 =  Ideal.span {B.equivFun.symm ![-2497, -1000, -128]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 605 ![![31, 0, 0], ![11, 1, 0]]
  ![451, -119, 8] ![![605, 0, 0], ![-212, 1, 0]] where
    su := ![![18755, 0, 0], ![6655, 605, 0]]
    hsu := by decide
    w := ![![272855, -71995, 4840], ![-94380, 26015, -1815]]
    hw := by decide
    g := ![![![20834455, 40387921877, -190509529], ![59456816, 115258265058, 0]], ![![7666749, 14862182711, -70104806], ![21879165, 42413407638, 0]]]
    h := ![![![1947374, 207485, 2769], ![-5488013, -85831, 0]], ![![-673364, -71761, -959], ![1897648, 29726, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {605} * I31N1 =  Ideal.span {B.equivFun.symm ![451, -119, 8]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS1 
