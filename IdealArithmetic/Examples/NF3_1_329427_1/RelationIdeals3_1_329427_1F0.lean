import IdealArithmetic.Examples.NF3_1_329427_1.PrimesBelow3_1_329427_1F0
import IdealArithmetic.Examples.NF3_1_329427_1.ClassGroupData3_1_329427_1

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


noncomputable def E2RS1 : RelationCertificate Table 4 ![![2, 0, 0], ![1, 1, 0]]
  ![155, 41, 10] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![8, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![620, 164, 40], ![1120, 296, 72]]
    hw := by decide
    g := ![![![422, 549020, 1166588], ![137256, -2333184, -15]], ![![-13, 7, 16], ![4, -31, 0]]]
    h := ![![![61, 4, 5], ![33, 0, 0]], ![![110, 7, 9], ![60, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {4} * I2N1 =  Ideal.span {B.equivFun.symm ![155, 41, 10]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 25 ![![3, 0, 0], ![1, 1, 0]]
  ![1879, 497, 121] ![![25, 0, 0], ![12, 1, 0]] where
    su := ![![75, 0, 0], ![25, 25, 0]]
    hsu := by decide
    w := ![![46975, 12425, 3025], ![36100, 9550, 2325]]
    hw := by decide
    g := ![![![-5420783, 347381591, 53512819], ![11293307, -668910238, 0]], ![![-1204621, 77195694, 11891704], ![2509627, -148646304, 0]]]
    h := ![![![-11288, -11650, 139], ![35743, -148, 0]], ![![-8674, -8952, 107], ![27466, -114, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {25} * I3N0 =  Ideal.span {B.equivFun.symm ![1879, 497, 121]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![-6, 2, 1]]
  ![141, 38, 9] ![![25, 0, 0], ![12, 1, 0]] where
    su := ![![125, 0, 0], ![-150, 50, 25]]
    hsu := by decide
    w := ![![3525, 950, 225], ![2700, 725, 175]]
    hw := by decide
    g := ![![![-843, 53366, 8221], ![1755, -102762, 0]], ![![1230, -79242, -12207], ![-2561, 152586, 0]]]
    h := ![![![15, 12, 4], ![-11, 0, 0]], ![![12, 9, 3], ![-8, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![141, 38, 9]} * (J0 ^ 0*J1^ 2) := by
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


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![0, 1, 0]]
  ![-7, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![-14, 2, 0], ![0, -6, 2]]
    hw := by decide
    g := ![![![-161, -11, 2], ![-4, 0, 3]], ![![-160, -11, 2], ![-4, 0, 3]]]
    h := ![![![-1, 0, 0], ![1, 0, 0]], ![![0, -2, -3], ![0, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-7, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E13RS1 : RelationCertificate Table 50 ![![13, 0, 0], ![-3, 1, 0]]
  ![117, 31, 8] ![![50, 0, 0], ![12, 1, 0]] where
    su := ![![650, 0, 0], ![-150, 50, 0]]
    hsu := by decide
    w := ![![5850, 1550, 400], ![2300, 600, 150]]
    hw := by decide
    g := ![![![-245923263, 54185691464, 8339413368], ![1024692276, -208485327123, -1287]], ![![75668343, -16672443507, -2565961502], ![-315288461, 64149035373, 396]]]
    h := ![![![18903, -6427, 132], ![81874, -854, 0]], ![![7432, -2526, 51], ![32190, -330, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {50} * I13N1 =  Ideal.span {B.equivFun.symm ![117, 31, 8]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 10 ![![17, 0, 0], ![1, 1, 0]]
  ![-37, -1, 2] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![170, 0, 0], ![10, 10, 0]]
    hsu := by decide
    w := ![![-370, -10, 20], ![150, -20, 0]]
    hw := by decide
    g := ![![![-32944462, 1710074819, 1151014192], ![164418597, -5755073670, 5424]], ![![-4118064, 213759731, 143877029], ![20552367, -719385483, 678]]]
    h := ![![![0, 2, 0], ![-37, 1, 0]], ![![-2, -3, 0], ![49, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {10} * I17N0 =  Ideal.span {B.equivFun.symm ![-37, -1, 2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 10 ![![17, 0, 0], ![4, 1, 0]]
  ![33, 9, 2] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![170, 0, 0], ![40, 10, 0]]
    hsu := by decide
    w := ![![330, 90, 20], ![290, 80, 20]]
    hw := by decide
    g := ![![![-124856358, 6496706906, 4372780340], ![624699427, -21863897970, -7458]], ![![-34051757, 1771830348, 1192577259], ![170372693, -5962885278, -2034]]]
    h := ![![![-11, 862, 346], ![55, -2940, 0]], ![![-11, 757, 304], ![54, -2583, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {10} * I17N1 =  Ideal.span {B.equivFun.symm ![33, 9, 2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 10 ![![17, 0, 0], ![-5, 1, 0]]
  ![-39, -7, 4] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![170, 0, 0], ![-50, 10, 0]]
    hsu := by decide
    w := ![![-390, -70, 40], ![370, -20, -10]]
    hw := by decide
    g := ![![![-22305, 211736, 143230], ![16722, -716990, 1695]], ![![1, 1, 1], ![10, -4, 0]]]
    h := ![![![-552, 114, -2], ![-1869, 19, 0]], ![![546, -107, -1], ![1849, 8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {10} * I17N2 =  Ideal.span {B.equivFun.symm ![-39, -7, 4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS2 


noncomputable def E19RS1 : RelationCertificate Table 100 ![![19, 0, 0], ![2, 1, 0]]
  ![327, -39, -2] ![![100, 0, 0], ![12, 1, 0]] where
    su := ![![1900, 0, 0], ![200, 100, 0]]
    hsu := by decide
    w := ![![32700, -3900, -200], ![3700, -200, -100]]
    hw := by decide
    g := ![![![634048, -624625999, -96114786], ![-6170121, 4805216955, 94975]], ![![76077, -74955158, -11533780], ![-740325, 576626325, 11397]]]
    h := ![![![54291, 27918, 522], ![-515601, -4960, 0]], ![![6149, 3162, 59], ![-58397, -561, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {100} * I19N1 =  Ideal.span {B.equivFun.symm ![327, -39, -2]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E19RS1 
