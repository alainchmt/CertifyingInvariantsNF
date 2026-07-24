import IdealArithmetic.Examples.NF3_1_190291_1.PrimesBelow3_1_190291_1F0
import IdealArithmetic.Examples.NF3_1_190291_1.ClassGroupData3_1_190291_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![80, -8, -17], ![2, 4, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![80, -8, -17], ![2, 4, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 4 ![![2, 0, 0], ![1, 1, 0]]
  ![7, -1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![8, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![28, -4, 0], ![12, 4, -8]]
    hw := by decide
    g := ![![![13, -4, 0], ![10, 0, -1]], ![![-10, 0, -1], ![-4, 0, 0]]]
    h := ![![![3, -1, 0], ![1, 0, 0]], ![![1, 0, -1], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {4} * I2N1 =  Ideal.span {B.equivFun.symm ![7, -1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0], ![3, -1, 1]]
  ![-3, 2, -2] ![![9, 0, 0], ![0, 1, 0]] where
    su := ![![27, 0, 0], ![27, -9, 9]]
    hsu := by decide
    w := ![![-27, 18, -18], ![-162, 9, 18]]
    hw := by decide
    g := ![![![431, 211, 1714], ![31, -1928, 0]], ![![215, 105, 857], ![20, -964, 0]]]
    h := ![![![1, 0, 0], ![-2, 0, 0]], ![![-5, 0, 1], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![-3, 2, -2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![-1, -4, -8], ![9, 3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-1, -4, -8], ![9, 3, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E11RS1 : RelationCertificate Table 6 ![![11, 0, 0], ![2, 1, 0]]
  ![-15, -1, 4] ![![6, 0, 0], ![0, 1, 0]] where
    su := ![![66, 0, 0], ![12, 6, 0]]
    hsu := by decide
    w := ![![-90, -6, 24], ![330, -36, -12]]
    hw := by decide
    g := ![![![-1184301, -556371, -4591597], ![-92723, 3444022, 2620]], ![![-236893, -111277, -918323], ![-18546, 688805, 524]]]
    h := ![![![75, 119, 324], ![25, -445, 0]], ![![-285, -451, -1222], ![-85, 1680, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {6} * I11N1 =  Ideal.span {B.equivFun.symm ![-15, -1, 4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 36 ![![11, 0, 0], ![-3, 1, 0]]
  ![-51, 1, 8] ![![36, 0, 0], ![18, 1, 0]] where
    su := ![![396, 0, 0], ![-108, 36, 0]]
    hsu := by decide
    w := ![![-1836, 36, 288], ![-252, -72, 144]]
    hw := by decide
    g := ![![![17469399640, 238490688806, 100596757914], ![15359441177, -452685477888, 31660]], ![![-3493880602, -47698146772, -20119355383], ![-3071888780, 90537112680, -6332]]]
    h := ![![![-122, 126, -520], ![47, 716, 0]], ![![-15, 16, -68], ![10, 94, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {36} * I11N2 =  Ideal.span {B.equivFun.symm ![-51, 1, 8]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E11RS2 


noncomputable def E17RS1 : RelationCertificate Table 9 ![![17, 0, 0], ![2, 1, 0]]
  ![6, -1, 1] ![![9, 0, 0], ![0, 1, 0]] where
    su := ![![153, 0, 0], ![18, 9, 0]]
    hsu := by decide
    w := ![![54, -9, 9], ![81, 0, -9]]
    hw := by decide
    g := ![![![-478, -237, -1919], ![-24, 2159, 0]], ![![-55, -28, -223], ![2, 251, 0]]]
    h := ![![![-52, -78, -207], ![5, 440, 0]], ![![-75, -114, -305], ![-6, 648, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {9} * I17N1 =  Ideal.span {B.equivFun.symm ![6, -1, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 18 ![![19, 0, 0], ![-6, 1, 0]]
  ![-51, -5, -4] ![![18, 0, 0], ![0, 1, 0]] where
    su := ![![342, 0, 0], ![-108, 18, 0]]
    hsu := by decide
    w := ![![-918, -90, -72], ![-342, -36, -36]]
    hw := by decide
    g := ![![![-4234655, -2082669, -16736449], ![-115691, 37658376, 10928]], ![![1058664, 520667, 4184115], ![28933, -9414600, -2732]]]
    h := ![![![95, -271, 436], ![-36, -1036, 0]], ![![37, -101, 162], ![-8, -385, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {18} * I19N1 =  Ideal.span {B.equivFun.symm ![-51, -5, -4]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 36 ![![23, 0, 0], ![6, 1, 0]]
  ![33, 5, 4] ![![36, 0, 0], ![18, 1, 0]] where
    su := ![![828, 0, 0], ![216, 36, 0]]
    hsu := by decide
    w := ![![1188, 180, 144], ![936, 108, 108]]
    hw := by decide
    g := ![![![11929095, 162854282, 68692899], ![10488298, -309118026, -9]], ![![3966014, 54143435, 22838021], ![3486996, -102771088, -3]]]
    h := ![![![-13, -39, -44], ![13, 127, 0]], ![![-10, -31, -35], ![9, 101, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {36} * I23N1 =  Ideal.span {B.equivFun.symm ![33, 5, 4]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E23RS1 
