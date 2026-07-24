import IdealArithmetic.Examples.NF3_1_466796_1.PrimesBelow3_1_466796_1F0
import IdealArithmetic.Examples.NF3_1_466796_1.ClassGroupData3_1_466796_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 49 ![![2, 0, 0], ![1, 1, 0]]
  ![99, -19, -2] ![![49, 0, 0], ![14, 1, 0]] where
    su := ![![98, 0, 0], ![49, 49, 0]]
    hsu := by decide
    w := ![![4851, -931, -98], ![2744, -441, -49]]
    hw := by decide
    g := ![![![-607, 110556, 7900], ![2128, -387099, 0]], ![![-405, 72341, 5169], ![1395, -253287, 0]]]
    h := ![![![66, 17, 9], ![-33, -20, 0]], ![![36, 9, 5], ![-16, -11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {49} * I2N0 =  Ideal.span {B.equivFun.symm ![99, -19, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS0 


noncomputable def E7RS0 : RelationCertificate Table 1 ![![7, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![7, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {1} * I7N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 49 ![![7, 0, 0], ![-95, 6, 1]]
  ![73, -15, 1] ![![49, 0, 0], ![14, 1, 0]] where
    su := ![![343, 0, 0], ![-4655, 294, 49]]
    hsu := by decide
    w := ![![3577, -735, 49], ![343, 0, 0]]
    hw := by decide
    g := ![![![7588, -1409986, -100752], ![-26557, 4936848, 0]], ![![-102885, 19082757, 1363579], ![360077, -66815368, 0]]]
    h := ![![![24, -3, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {49} * I7N1 =  Ideal.span {B.equivFun.symm ![73, -15, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 11 ![![11, 0, 0], ![1, 1, 0]]
  ![152, -15, -2] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![121, 0, 0], ![11, 11, 0]]
    hsu := by decide
    w := ![![1672, -165, -22], ![902, -77, -11]]
    hw := by decide
    g := ![![![4, -13, 4], ![1, -43, 0]], ![![-2, -3, 1], ![12, -12, 0]]]
    h := ![![![26, 10, -1], ![-134, 9, 0]], ![![14, 5, -1], ![-72, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {11} * I11N0 =  Ideal.span {B.equivFun.symm ![152, -15, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![-3, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![11, 0, 0], ![-3, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![-3, 1, 0]]
    hw := by decide
    g := ![![![19, -6, 0], ![66, 0, 0]], ![![-3, 4, -1], ![-10, 11, 0]]]
    h := ![![![19, -6, 0], ![66, 0, 0]], ![![-3, 4, -1], ![-10, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 539 ![![13, 0, 0], ![-92, 2, 1]]
  ![-1087, 367, -31] ![![539, 0, 0], ![63, 1, 0]] where
    su := ![![7007, 0, 0], ![-49588, 1078, 539]]
    hsu := by decide
    w := ![![-585893, 197813, -16709], ![-47432, 17787, -1617]]
    hw := by decide
    g := ![![![-12883687297386, 60224080511149625, 955941031970200], ![110227102433182, -515252216231937794, 0]], ![![91259451689393, -426587236952578718, -6771248976433396], ![-780775308898118, 3649703198297600429, 0]]]
    h := ![![![65, 25, -4], ![21, 0, 0]], ![![64, 1, -1], ![10, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {539} * I13N0 =  Ideal.span {B.equivFun.symm ![-1087, 367, -31]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 847 ![![13, 0, 0], ![-3, 1, 0]]
  ![-782, 53, 10] ![![847, 0, 0], ![-91, 1, 0]] where
    su := ![![11011, 0, 0], ![-2541, 847, 0]]
    hsu := by decide
    w := ![![-662354, 44891, 8470], ![64372, -4235, -847]]
    hw := by decide
    g := ![![![-973094, -7760388863, 85279116], ![-9057263, -72231411255, 0]], ![![172344, 1373724096, -15095890], ![1604124, 12786218829, 0]]]
    h := ![![![-2257226, 785686, -11097], ![-9781052, 144271, 0]], ![![219364, -76354, 1078], ![950552, -14015, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {847} * I13N1 =  Ideal.span {B.equivFun.symm ![-782, 53, 10]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 5929 ![![17, 0, 0], ![3, 1, 0]]
  ![26392, -2040, -305] ![![5929, 0, 0], ![-2632, 1, 0]] where
    su := ![![100793, 0, 0], ![17787, 5929, 0]]
    hsu := by decide
    w := ![![156478168, -12095160, -1808345], ![-69256649, 5353887, 800415]]
    hw := by decide
    g := ![![![3632, 46846960, -17799], ![8182, 105530256, 0]], ![![1097, 11975604, -4550], ![2471, 26976960, 0]]]
    h := ![![![25994, 8309, 76], ![-138502, -1597, 0]], ![![-11509, -3680, -34], ![61324, 713, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {5929} * I17N1 =  Ideal.span {B.equivFun.symm ![26392, -2040, -305]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 121 ![![19, 0, 0], ![9, 1, 0]]
  ![162, -28, -3] ![![121, 0, 0], ![30, 1, 0]] where
    su := ![![2299, 0, 0], ![1089, 121, 0]]
    hsu := by decide
    w := ![![19602, -3388, -363], ![6897, -1089, -121]]
    hw := by decide
    g := ![![![-20, 6389, 213], ![81, -25772, 0]], ![![-31, 3059, 102], ![124, -12342, 0]]]
    h := ![![![53262, 9490, 397], ![-112424, -7546, 0]], ![![18768, 3336, 139], ![-39615, -2642, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {121} * I19N1 =  Ideal.span {B.equivFun.symm ![162, -28, -3]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS1 


noncomputable def E29RS1 : RelationCertificate Table 77 ![![29, 0, 0], ![9, 1, 0]]
  ![-109, 13, 1] ![![77, 0, 0], ![-14, 1, 0]] where
    su := ![![2233, 0, 0], ![693, 77, 0]]
    hsu := by decide
    w := ![![-8393, 1001, 77], ![847, -154, 0]]
    hw := by decide
    g := ![![![10, -477, 34], ![40, -2620, 0]], ![![12, -155, 11], ![58, -848, 0]]]
    h := ![![![-338, -46, -1], ![1077, 30, 0]], ![![28, 3, 0], ![-89, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {77} * I29N1 =  Ideal.span {B.equivFun.symm ![-109, 13, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS1 


noncomputable def E31RS0 : RelationCertificate Table 539 ![![31, 0, 0], ![3, 1, 0]]
  ![-5270, 317, 54] ![![539, 0, 0], ![63, 1, 0]] where
    su := ![![16709, 0, 0], ![1617, 539, 0]]
    hsu := by decide
    w := ![![-2840530, 170863, 29106], ![-368676, 22099, 3773]]
    hw := by decide
    g := ![![![-43, -64890, -1030], ![366, 555165, 0]], ![![-53, -14617, -232], ![455, 125049, 0]]]
    h := ![![![-7408370, -2495705, -8770], ![76551400, 271924, 0]], ![![-961548, -323925, -1139], ![9935768, 35316, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {539} * I31N0 =  Ideal.span {B.equivFun.symm ![-5270, 317, 54]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 847 ![![31, 0, 0], ![4, 1, 0]]
  ![2059, 37, -9] ![![847, 0, 0], ![-91, 1, 0]] where
    su := ![![26257, 0, 0], ![3388, 847, 0]]
    hsu := by decide
    w := ![![1743973, 31339, -7623], ![-181258, -2541, 847]]
    hw := by decide
    g := ![![![99, 82171, -903], ![927, 764831, 0]], ![![25, 12558, -138], ![231, 116889, 0]]]
    h := ![![![2045, 501, 1], ![-15334, -40, 0]], ![![-218, -57, -1], ![1636, 32, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {847} * I31N1 =  Ideal.span {B.equivFun.symm ![2059, 37, -9]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS1 
