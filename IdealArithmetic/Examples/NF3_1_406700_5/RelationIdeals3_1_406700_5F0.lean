import IdealArithmetic.Examples.NF3_1_406700_5.PrimesBelow3_1_406700_5F0
import IdealArithmetic.Examples.NF3_1_406700_5.ClassGroupData3_1_406700_5

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 289 ![![2, 0, 0], ![1, 1, 0]]
  ![-1111, 17, -24] ![![289, 0, 0], ![84, 1, 0]] where
    su := ![![578, 0, 0], ![289, 289, 0]]
    hsu := by decide
    w := ![![-321079, 4913, -6936], ![-93636, 1445, -2023]]
    hw := by decide
    g := ![![![5519, -5970150, -71074], ![-18988, 20540385, 0]], ![![12929, -14027426, -166995], ![-44482, 48261555, 0]]]
    h := ![![![-742, -270, -104], ![373, 184, 0]], ![![-216, -79, -31], ![108, 55, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {289} * I2N0 =  Ideal.span {B.equivFun.symm ![-1111, 17, -24]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E2RS0 


noncomputable def E5RS0 : RelationCertificate Table 289 ![![5, 0, 0], ![-2, 1, 0]]
  ![488, -6, 11] ![![289, 0, 0], ![-53, 1, 0]] where
    su := ![![1445, 0, 0], ![-578, 289, 0]]
    hsu := by decide
    w := ![![141032, -1734, 3179], ![-25721, 289, -578]]
    hw := by decide
    g := ![![![9, 7685, -145], ![49, 41906, 0]], ![![42, -2810, 53], ![229, -15318, 0]]]
    h := ![![![357320, -197390, 9391], ![893056, -46944, 0]], ![![-65159, 35996, -1713], ![-162853, 8563, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {289} * I5N0 =  Ideal.span {B.equivFun.symm ![488, -6, 11]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 17 ![![7, 0, 0], ![2, 1, 0]]
  ![-2, -1, 0] ![![17, 0, 0], ![36, -3, 1]] where
    su := ![![119, 0, 0], ![34, 17, 0]]
    hsu := by decide
    w := ![![-34, -17, 0], ![-85, 17, 0]]
    hw := by decide
    g := ![![![-1, 0, 0], ![-1, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]
    h := ![![![-50, -29, -2], ![174, 14, 0]], ![![-115, -65, -4], ![400, 28, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {17} * I7N0 =  Ideal.span {B.equivFun.symm ![-2, -1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS0 


noncomputable def E17RS0 : RelationCertificate Table 289 ![![17, 0, 0], ![2, 1, 0]]
  ![3, -5, 1] ![![289, 0, 0], ![172, 31, 1]] where
    su := ![![4913, 0, 0], ![578, 289, 0]]
    hsu := by decide
    w := ![![867, -1445, 289], ![867, -2023, 0]]
    hw := by decide
    g := ![![![-28, -7, 0], ![64, 0, 0]], ![![-4, -1, 0], ![9, 0, 0]]]
    h := ![![![1477, 748, 5], ![-12553, -84, 0]], ![![1461, 740, 5], ![-12417, -85, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {289} * I17N0 =  Ideal.span {B.equivFun.symm ![3, -5, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 1 ![![17, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![17, 0, 0], ![-2, 1, 0]] where
    su := ![![17, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![17, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![23, -11, 0], ![187, 0, 0]], ![![-2, 3, -1], ![-16, 17, 0]]]
    h := ![![![23, -11, 0], ![187, 0, 0]], ![![-2, 3, -1], ![-16, 17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {1} * I17N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 1 ![![17, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![17, 0, 0], ![-1, 1, 0]] where
    su := ![![17, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![17, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![4, -3, 0], ![51, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![4, -3, 0], ![51, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {1} * I17N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS2 


noncomputable def E19RS1 : RelationCertificate Table 17 ![![19, 0, 0], ![3, 1, 0]]
  ![-45, 1, -1] ![![17, 0, 0], ![36, -3, 1]] where
    su := ![![323, 0, 0], ![51, 17, 0]]
    hsu := by decide
    w := ![![-765, 17, -17], ![-1581, 17, -34]]
    hw := by decide
    g := ![![![-32, 2, -1], ![15, 0, 0]], ![![-34, 3, -1], ![16, 0, 0]]]
    h := ![![![-1782, -614, -7], ![11271, 132, 0]], ![![-3684, -1265, -13], ![23301, 245, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {17} * I19N1 =  Ideal.span {B.equivFun.symm ![-45, 1, -1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 17 ![![23, 0, 0], ![-10, 1, 0]]
  ![655, -10, 14] ![![17, 0, 0], ![36, -3, 1]] where
    su := ![![391, 0, 0], ![-170, 17, 0]]
    hsu := by decide
    w := ![![11135, -170, 238], ![23086, -357, 493]]
    hw := by decide
    g := ![![![-3, -4, 0], ![2, 0, 0]], ![![-28, 4, -1], ![13, 0, 0]]]
    h := ![![![3035, -325, 3], ![6915, -55, 0]], ![![6286, -681, 7], ![14322, -132, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {17} * I23N0 =  Ideal.span {B.equivFun.symm ![655, -10, 14]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 289 ![![23, 0, 0], ![-9, 1, 0]]
  ![-23, 17, -7] ![![289, 0, 0], ![84, 1, 0]] where
    su := ![![6647, 0, 0], ![-2601, 289, 0]]
    hsu := by decide
    w := ![![-6647, 4913, -2023], ![-2023, 1734, -578]]
    hw := by decide
    g := ![![![1630494, -1758201051, -20931196], ![-5609680, 6049115636, 0]], ![![-630178, 679495293, 8089319], ![2168114, -2337813188, 0]]]
    h := ![![![-69877, 8653, -99], ![-178572, 2270, 0]], ![![-21317, 2638, -30], ![-54476, 688, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {289} * I23N1 =  Ideal.span {B.equivFun.symm ![-23, 17, -7]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 289 ![![23, 0, 0], ![-5, 1, 0]]
  ![-13841, 214, -296] ![![289, 0, 0], ![-53, 1, 0]] where
    su := ![![6647, 0, 0], ![-1445, 289, 0]]
    hsu := by decide
    w := ![![-4000049, 61846, -85544], ![729725, -11271, 15606]]
    hw := by decide
    g := ![![![-902707, -1470424934, 27744188], ![-4922308, -8018070344, 0]], ![![171320, 279007318, -5264350], ![934179, 1521397152, 0]]]
    h := ![![![-23218167, 4823463, -36001], ![-106800800, 827727, 0]], ![![4235675, -879938, 6567], ![19483600, -150987, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {289} * I23N2 =  Ideal.span {B.equivFun.symm ![-13841, 214, -296]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E23RS2 


noncomputable def E31RS0 : RelationCertificate Table 17 ![![31, 0, 0], ![1, 1, 0]]
  ![30, 0, 1] ![![17, 0, 0], ![-1, 1, 0]] where
    su := ![![527, 0, 0], ![17, 17, 0]]
    hsu := by decide
    w := ![![510, 0, 17], ![-17, -17, 0]]
    hw := by decide
    g := ![![![1, -29, 29], ![-1, -492, 0]], ![![1, -5, 4], ![16, -68, 0]]]
    h := ![![![0, -1, 0], ![30, 1, 0]], ![![0, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {17} * I31N0 =  Ideal.span {B.equivFun.symm ![30, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 17 ![![31, 0, 0], ![12, 1, 0]]
  ![-6, 20, 3] ![![17, 0, 0], ![-2, 1, 0]] where
    su := ![![527, 0, 0], ![204, 17, 0]]
    hsu := by decide
    w := ![![-102, 340, 51], ![51, -187, 17]]
    hw := by decide
    g := ![![![-142, 56, -31], ![34, 474, 0]], ![![-55, 27, -15], ![24, 234, 0]]]
    h := ![![![-42, -4, 0], ![108, 3, 0]], ![![9, 0, 0], ![-23, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {17} * I31N1 =  Ideal.span {B.equivFun.symm ![-6, 20, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 289 ![![31, 0, 0], ![-14, 1, 0]]
  ![139, -1, 3] ![![289, 0, 0], ![172, 31, 1]] where
    su := ![![8959, 0, 0], ![-4046, 289, 0]]
    hsu := by decide
    w := ![![40171, -289, 867], ![25143, -289, 578]]
    hw := by decide
    g := ![![![-2, -1, 0], ![4, 0, 0]], ![![-168, -30, -1], ![282, 0, 0]]]
    h := ![![![711209, -57589, 485], ![1574810, -15032, 0]], ![![445201, -36041, 303], ![985796, -9391, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {289} * I31N2 =  Ideal.span {B.equivFun.symm ![139, -1, 3]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS2 
