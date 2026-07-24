import IdealArithmetic.Examples.NF3_1_132328_2.PrimesBelow3_1_132328_2F0
import IdealArithmetic.Examples.NF3_1_132328_2.ClassGroupData3_1_132328_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![56, -16, -1], ![-6, 0, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![56, -16, -1], ![-6, 0, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![12, 2, 1]]
  ![-36951, 15223, -832] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![4, 0, 0], ![24, 4, 2]]
    hsu := by decide
    w := ![![-73902, 30446, -1664], ![-45760, -5920, 31278]]
    hw := by decide
    g := ![![![-2557457827, -166504366, -117804878], ![-83252182, 0, 21]], ![![-24307974257, -1582581627, -1119704996], ![-791290813, 0, 119]]]
    h := ![![![-212007, 760565, 71215], ![-475821, 110853, 0]], ![![-130942, 464803, 52201], ![-294683, 68640, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![-36951, 15223, -832]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![-3, 1, 0]]
  ![-3, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![-6, 2, 0], ![0, -2, 2]]
    hw := by decide
    g := ![![![-6694, 1846, 121], ![923, 0, 243]], ![![1486, -411, -27], ![-204, 0, -54]]]
    h := ![![![-15, 7, -2], ![-34, 7, 0]], ![![0, 3, -3], ![0, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-3, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![-2, 1, 0]]
  ![87, 7, 4] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![174, 14, 8], ![220, 18, 10]]
    hw := by decide
    g := ![![![9651, -2667, -176], ![-1333, 0, -351]], ![![-2231, 616, 41], ![309, 0, 81]]]
    h := ![![![13, 37, -72], ![2, 254, 0]], ![![18, 46, -91], ![8, 321, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![87, 7, 4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E11RS1 : RelationCertificate Table 4 ![![11, 0, 0], ![0, 1, 0]]
  ![620805669, 50522327, 28596350] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![44, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![2483222676, 202089308, 114385400], ![2814410588, 229042000, 129641004]]
    hw := by decide
    g := ![![![-2413076662, 24130708616, 16891493291], ![4826138827, -33782987040, -7]], ![![-2413071358, 24130705107, 16891494102], ![4826140601, -33782987040, -7]]]
    h := ![![![56436879, -96000726, -200174450], ![-8727337, 1115257650, 0]], ![![63963877, -108804363, -226871757], ![-9891296, 1263999789, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {4} * I11N1 =  Ideal.span {B.equivFun.symm ![620805669, 50522327, 28596350]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E17RS0 : RelationCertificate Table 4 ![![17, 0, 0], ![8, 1, 0]]
  ![-956927, 350467, 35534] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![68, 0, 0], ![32, 4, 0]]
    hsu := by decide
    w := ![![-3827708, 1401868, 142136], ![40516, -580672, 736468]]
    hw := by decide
    g := ![![![-155720853630, -1468426181279, -1050013978769], ![-444966972132, 2065185289675, 3375]], ![![-111181964155, -762913570877, -547742721371], ![-246319374793, 1073896350360, 1755]]]
    h := ![![![305265, -15503525, -3457762], ![-768304, 29408744, 0]], ![![-6431, 305162, 80737], ![14932, -594206, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {4} * I17N0 =  Ideal.span {B.equivFun.symm ![-956927, 350467, 35534]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![-4, 1, 0]]
  ![1, -5, 6] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![68, 0, 0], ![-16, 4, 0]]
    hsu := by decide
    w := ![![4, -20, 24], ![332, -128, -4]]
    hw := by decide
    g := ![![![211264948, -2113118394, -1479201073], ![-422647122, 2958399955, 4185]], ![![-47705093, 477155606, 334013025], ![95436358, -668025569, -945]]]
    h := ![![![1, 9, -6], ![4, 54, 0]], ![![11, 382, -257], ![26, 2184, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![1, -5, 6]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![4, 1, 0]]
  ![-4559, -371, -210] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![46, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![-9118, -742, -420], ![-11550, -940, -532]]
    hw := by decide
    g := ![![![-40027, 11057, 735], ![5529, 0, 1456]], ![![-9991, 2760, 182], ![1381, 0, 364]]]
    h := ![![![-1769, -466, -32], ![9032, 263, 0]], ![![-2241, -589, -40], ![11442, 327, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![-4559, -371, -210]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 
