import IdealArithmetic.Examples.NF3_1_933107_2.PrimesBelow3_1_933107_2F0
import IdealArithmetic.Examples.NF3_1_933107_2.ClassGroupData3_1_933107_2

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

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 4 ![![2, 0, 0], ![-25, 3, 1]]
  ![-41, -13, -1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![8, 0, 0], ![-100, 12, 4]]
    hsu := by decide
    w := ![![-164, -52, -4], ![136, -104, -16]]
    hw := by decide
    g := ![![![-22996, 230685, 121132], ![46178, -484515, 0]], ![![323399, -3230224, -1695756], ![-645853, 6783090, 0]]]
    h := ![![![17, -11, -2], ![3, 0, 0]], ![![17, -13, -2], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {4} * I2N1 =  Ideal.span {B.equivFun.symm ![-41, -13, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![-26, 2, 1]]
  ![-31, 2, 1] ![![25, 0, 0], ![-3, 1, 0]] where
    su := ![![125, 0, 0], ![-650, 50, 25]]
    hsu := by decide
    w := ![![-775, 50, 25], ![-125, 0, 0]]
    hw := by decide
    g := ![![![3, -7, 2], ![24, -50, 0]], ![![4, 29, -10], ![24, 250, 0]]]
    h := ![![![25, -2, -1], ![6, 0, 0]], ![![25, -2, -1], ![5, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![-31, 2, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![5, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![3, 1, 0], ![-5, 0, 0]], ![![-2, -1, 0], ![6, 0, 0]]]
    h := ![![![3, 1, 0], ![-5, 0, 0]], ![![-2, -1, 0], ![6, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 25 ![![7, 0, 0], ![2, 1, 0]]
  ![723, 34, -8] ![![25, 0, 0], ![-3, 1, 0]] where
    su := ![![175, 0, 0], ![50, 25, 0]]
    hsu := by decide
    w := ![![18075, 850, -200], ![-425, 325, 50]]
    hw := by decide
    g := ![![![-192, 79, -14], ![41, 178, 0]], ![![158, -37, 2], ![0, 88, 0]]]
    h := ![![![25213, 13874, 656], ![-87884, -4600, 0]], ![![-543, -301, -16], ![1892, 114, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {25} * I7N0 =  Ideal.span {B.equivFun.symm ![723, 34, -8]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 10 ![![11, 0, 0], ![1, 1, 0]]
  ![-81, -3, 1] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![110, 0, 0], ![10, 10, 0]]
    hsu := by decide
    w := ![![-810, -30, 10], ![-380, -50, 0]]
    hw := by decide
    g := ![![![-15, -9, -7], ![3, 65, 0]], ![![7, -6, -1], ![8, 13, 0]]]
    h := ![![![-8, -8, -7], ![7, 78, 0]], ![![-4, -4, -3], ![6, 33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {10} * I11N0 =  Ideal.span {B.equivFun.symm ![-81, -3, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 25 ![![11, 0, 0], ![4, 1, 0]]
  ![-49003, 14751, -1712] ![![25, 0, 0], ![-3, 1, 0]] where
    su := ![![275, 0, 0], ![100, 25, 0]]
    hsu := by decide
    w := ![![-1225075, 368775, -42800], ![520225, -156600, 18175]]
    hw := by decide
    g := ![![![-34, -1653, 549], ![-41, -13734, 0]], ![![-29, -5766, 1922], ![-213, -48069, 0]]]
    h := ![![![-46733, -10930, -581], ![116265, 4679, 0]], ![![19839, 4637, 246], ![-49355, -1979, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {25} * I11N1 =  Ideal.span {B.equivFun.symm ![-49003, 14751, -1712]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 4 ![![11, 0, 0], ![5, 1, 0]]
  ![-8501, 2559, -297] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![44, 0, 0], ![20, 4, 0]]
    hsu := by decide
    w := ![![-34004, 10236, -1188], ![47744, -14372, 1668]]
    hw := by decide
    g := ![![![-125, 19, 0], ![-55, 18, 0]], ![![-129, 17, 1], ![-59, 11, 0]]]
    h := ![![![-60141, -17201, -1139], ![130610, 12232, 0]], ![![84426, 24142, 1598], ![-183350, -17161, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {4} * I11N2 =  Ideal.span {B.equivFun.symm ![-8501, 2559, -297]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 50 ![![13, 0, 0], ![-30, 8, 1]]
  ![-352321, 106057, -12309] ![![50, 0, 0], ![22, 1, 0]] where
    su := ![![650, 0, 0], ![-1500, 400, 50]]
    hsu := by decide
    w := ![![-17616050, 5302850, -615450], ![-5067700, 1525500, -177050]]
    hw := by decide
    g := ![![![-1115769439, 151338909282, 6881346640], ![2535839638, -344067331981, 0]], ![![2637273110, -357710149189, -16265001145], ![-5993802781, 813250057388, 0]]]
    h := ![![![-3877, 1965, -1721], ![10064, 0, 0]], ![![-1118, 566, -495], ![2894, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {50} * I13N0 =  Ideal.span {B.equivFun.symm ![-352321, 106057, -12309]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 20 ![![13, 0, 0], ![4, 1, 0]]
  ![203, -61, 7] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![260, 0, 0], ![80, 20, 0]]
    hsu := by decide
    w := ![![4060, -1220, 140], ![-1120, 340, -40]]
    hw := by decide
    g := ![![![-3811, 768617, 385260], ![38065, -7705197, 0]], ![![-1078, 216789, 108663], ![10741, -2173258, 0]]]
    h := ![![![8947, 2570, 86], ![-29027, -1111, 0]], ![![-2472, -711, -24], ![8020, 310, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {20} * I13N1 =  Ideal.span {B.equivFun.symm ![203, -61, 7]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 25 ![![17, 0, 0], ![7, 1, 0]]
  ![-87, 4, 2] ![![25, 0, 0], ![-3, 1, 0]] where
    su := ![![425, 0, 0], ![175, 25, 0]]
    hsu := by decide
    w := ![![-2175, 100, 50], ![-175, -25, 0]]
    hw := by decide
    g := ![![![-1, 18, -6], ![10, 148, 0]], ![![3, 5, -2], ![24, 50, 0]]]
    h := ![![![-148, -28, -1], ![347, 19, 0]], ![![-14, -9, -1], ![33, 17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {25} * I17N1 =  Ideal.span {B.equivFun.symm ![-87, 4, 2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 5 ![![19, 0, 0], ![-5, 1, 0]]
  ![4179, -1258, 146] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![95, 0, 0], ![-25, 5, 0]]
    hsu := by decide
    w := ![![20895, -6290, 730], ![-23470, 7065, -820]]
    hw := by decide
    g := ![![![-153, 519, 265], ![45, -1311, 0]], ![![11, -146, -74], ![-19, 368, 0]]]
    h := ![![![6331, -1340, 18], ![23222, -196, 0]], ![![-7106, 1508, -21], ![-26064, 235, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {5} * I19N1 =  Ideal.span {B.equivFun.symm ![4179, -1258, 146]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 100 ![![23, 0, 0], ![1, 1, 0]]
  ![-231, -23, 1] ![![100, 0, 0], ![22, 1, 0]] where
    su := ![![2300, 0, 0], ![100, 100, 0]]
    hsu := by decide
    w := ![![-23100, -2300, 100], ![-5300, -700, 0]]
    hw := by decide
    g := ![![![-1689, 805055, 36597], ![7686, -3659693, 0]], ![![-14, -22, -1], ![61, 98, 0]]]
    h := ![![![-11, -11, -9], ![22, 208, 0]], ![![-3, -3, -2], ![16, 46, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {100} * I23N0 =  Ideal.span {B.equivFun.symm ![-231, -23, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![5, 1, 0]]
  ![143, -43, 5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![46, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![286, -86, 10], ![-1090, 328, -38]]
    hw := by decide
    g := ![![![68, -2, 499], ![-1, -1001, 0]], ![![29, 0, 136], ![0, -273, 0]]]
    h := ![![![856, 177, 2], ![-3909, -41, 0]], ![![-3280, -685, -9], ![14979, 188, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![143, -43, 5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 5 ![![23, 0, 0], ![-7, 1, 0]]
  ![-603, 96, 23] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![115, 0, 0], ![-35, 5, 0]]
    hsu := by decide
    w := ![![-3015, 480, 115], ![-6220, 440, 165]]
    hw := by decide
    g := ![![![5809, -2369, 215], ![1850, 69, 0]], ![![-3691, 1497, -141], ![-1177, -22, 0]]]
    h := ![![![-2433, 376, -3], ![-7908, 92, 0]], ![![-5018, 765, -6], ![-16310, 171, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {5} * I23N2 =  Ideal.span {B.equivFun.symm ![-603, 96, 23]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E23RS2 


noncomputable def E29RS1 : RelationCertificate Table 50 ![![29, 0, 0], ![14, 1, 0]]
  ![2087, -629, 73] ![![50, 0, 0], ![22, 1, 0]] where
    su := ![![1450, 0, 0], ![700, 50, 0]]
    hsu := by decide
    w := ![![104350, -31450, 3650], ![30000, -9050, 1050]]
    hw := by decide
    g := ![![![230845, -31314011, -1423841], ![-524669, 71192054, 0]], ![![113536, -15401902, -700321], ![-258048, 35016051, 0]]]
    h := ![![![384511, 47115, 1408], ![-796338, -40759, 0]], ![![110528, 13533, 404], ![-228908, -11695, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {50} * I29N1 =  Ideal.span {B.equivFun.symm ![2087, -629, 73]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 4 ![![31, 0, 0], ![8, 1, 0]]
  ![-55, -91, -11] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![124, 0, 0], ![32, 4, 0]]
    hsu := by decide
    w := ![![-220, -364, -44], ![2288, -644, -124]]
    hw := by decide
    g := ![![![5213, 7973, 5955], ![4601, -22770, 0]], ![![-230, 3028, 1612], ![646, -6435, 0]]]
    h := ![![![-57, -15, -1], ![214, 20, 0]], ![![564, 63, -1], ![-2114, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4} * I31N1 =  Ideal.span {B.equivFun.symm ![-55, -91, -11]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E31RS1 
