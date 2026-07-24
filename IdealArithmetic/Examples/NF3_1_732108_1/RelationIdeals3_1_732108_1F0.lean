import IdealArithmetic.Examples.NF3_1_732108_1.PrimesBelow3_1_732108_1F0
import IdealArithmetic.Examples.NF3_1_732108_1.ClassGroupData3_1_732108_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 3 ![![2, 0, 0], ![1, 1, 0]]
  ![-13, 11, 4] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![6, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![-39, 33, 12], ![126, -123, 51]]
    hw := by decide
    g := ![![![3851, 13, 32], ![7, 51, 0]], ![![4069, 6, 10], ![2, 68, 0]]]
    h := ![![![-137, 175, 302], ![21, -120, 0]], ![![470, -609, -1029], ![-68, 415, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {3} * I2N0 =  Ideal.span {B.equivFun.symm ![-13, 11, 4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![-3, 3, 10], ![3, -6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-3, 3, 10], ![3, -6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![-1, 1, 0]]
  ![620, 8, 19] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![9, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![1860, 24, 57], ![687, 9, 21]]
    hw := by decide
    g := ![![![-18, 16, 43], ![6, -26, 0]], ![![-39, 34, 88], ![13, -52, 0]]]
    h := ![![![898, -278, -2047], ![-390, 1232, 0]], ![![332, -103, -756], ![-143, 455, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![620, 8, 19]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![1, 1, 0]]
  ![1302, 17, 40] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![125, 0, 0], ![25, 25, 0]]
    hsu := by decide
    w := ![![32550, 425, 1000], ![4050, 50, 125]]
    hw := by decide
    g := ![![![-82153, 185626, 254221], ![853, -1268484, -13104]], ![![-15648, 35357, 48423], ![164, -241616, -2496]]]
    h := ![![![250, -7, 8], ![52, 0, 0]], ![![31, -1, 1], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![1302, 17, 40]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![5, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![102, -104, 3], ![25, 0, -15]], ![![33, -35, 1], ![11, 0, -5]]]
    h := ![![![102, -104, 3], ![25, 0, -15]], ![![33, -35, 1], ![11, 0, -5]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 15 ![![7, 0, 0], ![1, 1, 0]]
  ![2545814, 32904, 78035] ![![15, 0, 0], ![20, 1, 1]] where
    su := ![![105, 0, 0], ![15, 15, 0]]
    hsu := by decide
    w := ![![38187210, 493560, 1170525], ![54252900, 701205, 1662975]]
    hw := by decide
    g := ![![![7768, -13824, -9669], ![8814, 0, -10480]], ![![1927, -3462, -2391], ![2215, 0, -2620]]]
    h := ![![![-1818576, 3207244, 5395955], ![198386, -7538730, 0]], ![![-2583666, 4556560, 7666080], ![281844, -10710339, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {15} * I7N0 =  Ideal.span {B.equivFun.symm ![2545814, 32904, 78035]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 15 ![![7, 0, 0], ![2, 1, 0]]
  ![-162, -2, -5] ![![15, 0, 0], ![20, 1, 1]] where
    su := ![![105, 0, 0], ![30, 15, 0]]
    hsu := by decide
    w := ![![-2430, -30, -75], ![-3450, -45, -105]]
    hw := by decide
    g := ![![![-12068, 21446, 14961], ![-13647, 0, 16213]], ![![-5077, 8993, 6273], ![-5711, 0, 6799]]]
    h := ![![![-18848, 37653, 47065], ![-5, -65892, 0]], ![![-26756, 53448, 66809], ![-3, -93534, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {15} * I7N1 =  Ideal.span {B.equivFun.symm ![-162, -2, -5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 15 ![![7, 0, 0], ![3, 1, 0]]
  ![-4, 1, 0] ![![15, 0, 0], ![20, 1, 1]] where
    su := ![![105, 0, 0], ![45, 15, 0]]
    hsu := by decide
    w := ![![-60, 15, 0], ![-45, -15, 0]]
    hw := by decide
    g := ![![![-13, 13, 9], ![-6, 0, 10]], ![![-16, 6, 4], ![4, 0, 5]]]
    h := ![![![-610, 1565, 1560], ![-34, -2184, 0]], ![![-407, 1043, 1040], ![-22, -1456, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {15} * I7N2 =  Ideal.span {B.equivFun.symm ![-4, 1, 0]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS2 


noncomputable def E11RS0 : RelationCertificate Table 15 ![![11, 0, 0], ![25, 3, 1]]
  ![27, -28, 20] ![![15, 0, 0], ![20, 1, 1]] where
    su := ![![165, 0, 0], ![375, 45, 15]]
    hsu := by decide
    w := ![![405, -420, 300], ![120, -45, -345]]
    hw := by decide
    g := ![![![249, 2, 10], ![338, 0, 12]], ![![647, 1, 23], ![880, 0, 28]]]
    h := ![![![-18, -5, 1], ![9, 0, 0]], ![![-22, -3, -3], ![10, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {15} * I11N0 =  Ideal.span {B.equivFun.symm ![27, -28, 20]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 75 ![![11, 0, 0], ![-3, 1, 0]]
  ![1538, -1102, -1565] ![![75, 0, 0], ![27, 1, 0]] where
    su := ![![825, 0, 0], ![-225, 75, 0]]
    hsu := by decide
    w := ![![115350, -82650, -117375], ![-14175, 21225, -46200]]
    hw := by decide
    g := ![![![-2746988706, 42076545690, 7253532117], ![-427895266, -108803679536, 177332]], ![![447180225, -6849670249, -1180807688], ![69655982, 17712226852, -28868]]]
    h := ![![![10300, 5504, -27115], ![-2306, 59340, 0]], ![![-1391, -733, 3594], ![316, -8030, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {75} * I11N1 =  Ideal.span {B.equivFun.symm ![1538, -1102, -1565]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 15 ![![13, 0, 0], ![4, 1, 0]]
  ![-9529471, -123166, -292100] ![![15, 0, 0], ![-3, 1, 0]] where
    su := ![![195, 0, 0], ![60, 15, 0]]
    hsu := by decide
    w := ![![-142942065, -1847490, -4381500], ![18027045, 232995, 552570]]
    hw := by decide
    g := ![![![-58102994, -30647909, 150046480], ![9577405, -450139536, -72]], ![![-17753733, -9364604, 45847554], ![2926445, -137542636, -22]]]
    h := ![![![-9024467, 25667168, 21323300], ![-802350, -55499000, 0]], ![![1138111, -3236999, -2689174], ![101200, 6999220, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {15} * I13N0 =  Ideal.span {B.equivFun.symm ![-9529471, -123166, -292100]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS0 


noncomputable def E17RS1 : RelationCertificate Table 75 ![![17, 0, 0], ![3, 1, 0]]
  ![-38, 27, 40] ![![75, 0, 0], ![5, 1, 1]] where
    su := ![![1275, 0, 0], ![225, 75, 0]]
    hsu := by decide
    w := ![![-2850, 2025, 3000], ![1875, -1500, -1050]]
    hw := by decide
    g := ![![![-8141, 6795, -1005], ![-444, 19544, 6]], ![![-1289, 1133, -166], ![-25, 3258, 1]]]
    h := ![![![30, -81, -80], ![4, 280, 0]], ![![-12, 27, 28], ![11, -98, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {75} * I17N1 =  Ideal.span {B.equivFun.symm ![-38, 27, 40]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 15 ![![19, 0, 0], ![6, 1, 0]]
  ![-1469, -19, -45] ![![15, 0, 0], ![20, 1, 1]] where
    su := ![![285, 0, 0], ![90, 15, 0]]
    hsu := by decide
    w := ![![-22035, -285, -675], ![-31305, -405, -960]]
    hw := by decide
    g := ![![![-1042, 1835, 1280], ![-1161, 0, 1387]], ![![-274, 482, 337], ![-305, 0, 365]]]
    h := ![![![-21653, 89107, 55620], ![-2132, -211365, 0]], ![![-30761, 126594, 79019], ![-3033, -300285, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {15} * I19N0 =  Ideal.span {B.equivFun.symm ![-1469, -19, -45]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E19RS0 


noncomputable def E23RS1 : RelationCertificate Table 15 ![![23, 0, 0], ![11, 1, 0]]
  ![69326, 896, 2125] ![![15, 0, 0], ![-3, 1, 0]] where
    su := ![![345, 0, 0], ![165, 15, 0]]
    hsu := by decide
    w := ![![1039890, 13440, 31875], ![-131145, -1695, -4020]]
    hw := by decide
    g := ![![![239379, 132055, -628043], ![-39071, 1885490, 1702]], ![![104077, 57416, -273061], ![-16986, 819779, 740]]]
    h := ![![![586940, -4116200, -1581375], ![101746, 7274750, 0]], ![![-74029, 519111, 199434], ![-12816, -917450, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {15} * I23N1 =  Ideal.span {B.equivFun.symm ![69326, 896, 2125]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 15 ![![29, 0, 0], ![-11, 1, 0]]
  ![-32, 28, 5] ![![15, 0, 0], ![-3, 1, 0]] where
    su := ![![435, 0, 0], ![-165, 15, 0]]
    hsu := by decide
    w := ![![-480, 420, 75], ![225, -225, 120]]
    hw := by decide
    g := ![![![-206547, -109165, 534865], ![34046, -1604512, 29]], ![![85516, 45172, -221322], ![-14083, 663936, -12]]]
    h := ![![![-303, -1523, 845], ![95, -4900, 0]], ![![153, 717, -398], ![-18, 2310, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {15} * I29N1 =  Ideal.span {B.equivFun.symm ![-32, 28, 5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS1 
