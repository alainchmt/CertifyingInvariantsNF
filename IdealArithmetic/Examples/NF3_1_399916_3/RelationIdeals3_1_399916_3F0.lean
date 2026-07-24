import IdealArithmetic.Examples.NF3_1_399916_3.PrimesBelow3_1_399916_3F0
import IdealArithmetic.Examples.NF3_1_399916_3.ClassGroupData3_1_399916_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 11 ![![2, 0, 0], ![0, 0, 1]]
  ![-25, 7, -1] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![22, 0, 0], ![0, 0, 11]]
    hsu := by decide
    w := ![![-275, 77, -11], ![-165, -11, 11]]
    hw := by decide
    g := ![![![-8, 3, 4], ![0, -25, 0]], ![![-107, -14, -5], ![-19, -5, 0]]]
    h := ![![![-43, -16009, -2], ![265, -262, 525]], ![![-38, -9608, 0], ![158, -157, 315]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {11} * I2N0 =  Ideal.span {B.equivFun.symm ![-25, 7, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E11RS0 : RelationCertificate Table 1 ![![11, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![11, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![-17, -36, -36], ![0, 198, 0]], ![![-3, -6, -6], ![1, 33, 0]]]
    h := ![![![-17, -36, -36], ![0, 198, 0]], ![![-3, -6, -6], ![1, 33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {1} * I11N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 11 ![![11, 0, 0], ![4, 1, 0]]
  ![30, -37, 10] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![121, 0, 0], ![44, 11, 0]]
    hsu := by decide
    w := ![![330, -407, 110], ![1243, -44, -44]]
    hw := by decide
    g := ![![![-11468, -24708, -25132], ![-4321, 138320, 0]], ![![-4343, -9716, -9898], ![-1670, 54530, 0]]]
    h := ![![![11, 42, 24], ![9, -127, 0]], ![![32, 122, 62], ![26, -343, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {11} * I11N1 =  Ideal.span {B.equivFun.symm ![30, -37, 10]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E19RS1 : RelationCertificate Table 11 ![![19, 0, 0], ![-3, 1, 0]]
  ![823399, 123852, 43855] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![209, 0, 0], ![-33, 11, 0]]
    hsu := by decide
    w := ![![9057389, 1362372, 482405], ![7120960, 1071103, 379269]]
    hw := by decide
    g := ![![![106, -6, 83], ![29, -360, 0]], ![![91, 10, -12], ![23, 16, 0]]]
    h := ![![![-49886663, 156583072, -104947607], ![16118066, 997024194, 0]], ![![-39221119, 123106316, -82510281], ![12672096, 783864909, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {11} * I19N1 =  Ideal.span {B.equivFun.symm ![823399, 123852, 43855]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 121 ![![23, 0, 0], ![2, 1, 0]]
  ![-14274, 6741, -1414] ![![121, 0, 0], ![-31, 1, 0]] where
    su := ![![2783, 0, 0], ![242, 121, 0]]
    hsu := by decide
    w := ![![-1727154, 815661, -171094], ![276727, -223245, 55902]]
    hw := by decide
    g := ![![![-73321, -22892, -3472], ![18603, -42700, 0]], ![![-27622, -6059, -1470], ![7111, -6104, 0]]]
    h := ![![![52753, 108254, 108304], ![9305, -1246203, 0]], ![![-8682, -17842, -17808], ![-1525, 205023, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {121} * I23N0 =  Ideal.span {B.equivFun.symm ![-14274, 6741, -1414]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 11 ![![23, 0, 0], ![3, 1, 0]]
  ![2177581, 327542, 115980] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![253, 0, 0], ![33, 11, 0]]
    hsu := by decide
    w := ![![23953391, 3602962, 1275780], ![18832264, 2832665, 1003024]]
    hw := by decide
    g := ![![![21001, 42644, 43456], ![7698, -238994, 0]], ![![3642, 7472, 7570], ![1343, -41685, 0]]]
    h := ![![![-175186810, -541974413, -362666076], ![-46414551, 4170717864, 0]], ![![-137732660, -426102727, -285129704], ![-36491328, 3279037188, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {11} * I23N1 =  Ideal.span {B.equivFun.symm ![2177581, 327542, 115980]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 121 ![![29, 0, 0], ![4, 1, 0]]
  ![-1303, 118, 24] ![![121, 0, 0], ![-31, 1, 0]] where
    su := ![![3509, 0, 0], ![484, 121, 0]]
    hsu := by decide
    w := ![![-157663, 14278, 2904], ![43439, -4961, -484]]
    hw := by decide
    g := ![![![-243, 6462, -422], ![177, 25275, 0]], ![![-51, 1180, -78], ![64, 4625, 0]]]
    h := ![![![3345277, 13867298, 6949848], ![939612, -100772784, 0]], ![![-922672, -3824781, -1916858], ![-259148, 27794439, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {121} * I29N0 =  Ideal.span {B.equivFun.symm ![-1303, 118, 24]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 11 ![![29, 0, 0], ![9, 1, 0]]
  ![25, 4, 1] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![319, 0, 0], ![99, 11, 0]]
    hsu := by decide
    w := ![![275, 44, 11], ![176, 33, 11]]
    hw := by decide
    g := ![![![1458, 3061, 3111], ![544, -17110, 0]], ![![441, 928, 944], ![175, -5192, 0]]]
    h := ![![![-2854, -31015, -6907], ![-1929, 100152, 0]], ![![-1822, -19807, -4411], ![-1234, 63960, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {11} * I29N1 =  Ideal.span {B.equivFun.symm ![25, 4, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 121 ![![31, 0, 0], ![10, 1, 0]]
  ![4119980, 619709, 219434] ![![121, 0, 0], ![-31, 1, 0]] where
    su := ![![3751, 0, 0], ![1210, 121, 0]]
    hsu := by decide
    w := ![![498517580, 74984789, 26551514], ![-100328723, -15090999, -5343602]]
    hw := by decide
    g := ![![![-616, 18323, -1180], ![336, 71484, 0]], ![![-189, 6312, -406], ![172, 24642, 0]]]
    h := ![![![-11232739849, -138130278790, -27678177064], ![-8079279891, 429011854209, 0]], ![![2260635302, 27799289398, 5570347508], ![1625988493, -86340408455, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {121} * I31N1 =  Ideal.span {B.equivFun.symm ![4119980, 619709, 219434]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 
