import IdealArithmetic.Examples.NF3_1_186731_1.PrimesBelow3_1_186731_1F0
import IdealArithmetic.Examples.NF3_1_186731_1.ClassGroupData3_1_186731_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![0, 1, 0]]
  ![-16362, 1283, -1586] ![![2, 0, 0], ![2, 1, 1]] where
    su := ![![4, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![-32724, 2566, -3172], ![-46548, 3650, -4512]]
    hw := by decide
    g := ![![![-3, 10, 8], ![9, 0, 0]], ![![-311, 98, 152], ![-186, 0, 0]]]
    h := ![![![-7458, -77512, 1376], ![157271, -482, 0]], ![![-10608, -110256, 1959], ![223709, -686, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![-16362, 1283, -1586]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![2, 1, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![2, 1, 1]] where
    su := ![![2, 0, 0], ![2, 1, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![2, 1, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 3 ![![3, 0, 0], ![0, 1, 0]]
  ![933, 73, -36] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![9, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![2799, 219, -108], ![4140, 1224, 657]]
    hw := by decide
    g := ![![![-289947, 51327, -30675], ![-79537, 0, 0]], ![![800308, -141675, 84669], ![219545, 0, 0]]]
    h := ![![![24064, 1162, -5881], ![-5667, 2060, 933]], ![![35535, 1900, -8782], ![-8742, 3105, 1380]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {3} * I3N0 =  Ideal.span {B.equivFun.symm ![933, 73, -36]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 2 ![![3, 0, 0], ![0, -1, -1]]
  ![-1393, -209, -37] ![![2, 0, 0], ![2, 1, 1]] where
    su := ![![6, 0, 0], ![0, -2, -2]]
    hsu := by decide
    w := ![![-2786, -418, -74], ![16006, -1404, -3028]]
    hw := by decide
    g := ![![![987738, -464248, -173796], ![668719, 0, 0]], ![![-278177, 130746, 48946], ![-188331, 0, 0]]]
    h := ![![![-11, -798, -786], ![-2185, -17, 0]], ![![1, 3548, 3544], ![11346, 100, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {2} * I3N1 =  Ideal.span {B.equivFun.symm ![-1393, -209, -37]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 6 ![![3, 0, 0], ![0, 0, 1]]
  ![97, 4, -7] ![![6, 0, 0], ![4, 1, 3]] where
    su := ![![18, 0, 0], ![0, 0, 6]]
    hsu := by decide
    w := ![![582, 24, -42], ![-582, 300, 336]]
    hw := by decide
    g := ![![![-1262, 252, 182], ![-699, 0, 0]], ![![-3829, 769, 561], ![-2141, 0, 0]]]
    h := ![![![60, 2, 54], ![-168, 1, 0]], ![![23, 18, -26], ![136, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {6} * I3N2 =  Ideal.span {B.equivFun.symm ![97, 4, -7]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E3RS2 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![4, 1, 0]]
  ![-12906, 1012, -1251] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![51, 0, 0], ![12, 3, 0]]
    hsu := by decide
    w := ![![-38718, 3036, -3753], ![93963, -7368, 9108]]
    hw := by decide
    g := ![![![-217, 19, 24], ![-64, 0, 0]], ![![-157, -1, 3], ![-50, 0, 0]]]
    h := ![![![-28172, -58920, -89433], ![-10088, 168790, 0]], ![![68364, 142989, 217041], ![24505, -409629, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![-12906, 1012, -1251]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS1 


noncomputable def E23RS0 : RelationCertificate Table 6 ![![23, 0, 0], ![5, 1, 0]]
  ![4486501, -351802, 434885] ![![6, 0, 0], ![4, 1, 3]] where
    su := ![![138, 0, 0], ![30, 6, 0]]
    hsu := by decide
    w := ![![26919006, -2110812, 2609310], ![103619526, -8125164, 10044036]]
    hw := by decide
    g := ![![![452, 422, 144], ![449, 0, 0]], ![![-881, 207, 424], ![-331, 0, 0]]]
    h := ![![![1046615893, 2599569524, 3361379203], ![340549978, -8590142976, 0]], ![![4028746200, 10006541919, 12938981466], ![1310881445, -33066099968, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {6} * I23N0 =  Ideal.span {B.equivFun.symm ![4486501, -351802, 434885]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![6, 1, 0]]
  ![240571, -18864, 23319] ![![2, 0, 0], ![2, 1, 1]] where
    su := ![![46, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![481142, -37728, 46638], ![684398, -53666, 66340]]
    hw := by decide
    g := ![![![871, -269, -422], ![529, 0, 0]], ![![551, -118, -227], ![382, 0, 0]]]
    h := ![![![-687511, -2036786, -2302551], ![-267890, 5886888, 0]], ![![-977941, -2897215, -3275252], ![-381080, 8373774, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![240571, -18864, 23319]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 3 ![![23, 0, 0], ![11, 1, 0]]
  ![-52, 4, -5] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![69, 0, 0], ![33, 3, 0]]
    hsu := by decide
    w := ![![-156, 12, -15], ![375, -30, 36]]
    hw := by decide
    g := ![![![-15, 1, 2], ![-2, 0, 0]], ![![-14, 0, 1], ![-2, 0, 0]]]
    h := ![![![-6677, -38815, -27019], ![-4875, 69048, 0]], ![![16043, 93318, 64959], ![11741, -166005, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {3} * I23N2 =  Ideal.span {B.equivFun.symm ![-52, 4, -5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E23RS2 


noncomputable def E29RS0 : RelationCertificate Table 3 ![![29, 0, 0], ![7, 1, 0]]
  ![-3246, -554, -147] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![87, 0, 0], ![21, 3, 0]]
    hsu := by decide
    w := ![![-9738, -1662, -441], ![7293, -4614, -4986]]
    hw := by decide
    g := ![![![-6566083, 1162363, -694662], ![-1801240, 0, 0]], ![![289946, -51328, 30675], ![79540, 0, 0]]]
    h := ![![![-583979, -1893861, -1900959], ![-206249, 6125296, 0]], ![![451498, 1464175, 1469670], ![159479, -4735788, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {3} * I29N0 =  Ideal.span {B.equivFun.symm ![-3246, -554, -147]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E29RS0 


noncomputable def E31RS1 : RelationCertificate Table 6 ![![31, 0, 0], ![0, 1, 0]]
  ![-497, 5, 59] ![![6, 0, 0], ![4, 1, 3]] where
    su := ![![186, 0, 0], ![0, 6, 0]]
    hsu := by decide
    w := ![![-2982, 30, 354], ![-3336, -2208, -1638]]
    hw := by decide
    g := ![![![44607, -8965, -6548], ![24971, 0, 0]], ![![-11918, 2394, 1747], ![-6666, 0, 0]]]
    h := ![![![8449, 5637, 25397], ![202, -87472, 0]], ![![9452, 6294, 28401], ![230, -97856, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {6} * I31N1 =  Ideal.span {B.equivFun.symm ![-497, 5, 59]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E31RS1 
