import IdealArithmetic.Examples.NF3_1_230175_1.PrimesBelow3_1_230175_1F0
import IdealArithmetic.Examples.NF3_1_230175_1.ClassGroupData3_1_230175_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 11 ![![3, 0, 0], ![0, 1, 0]]
  ![18, 5, -3] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![33, 0, 0], ![0, 11, 0]]
    hsu := by decide
    w := ![![198, 55, -33], ![-297, -22, 22]]
    hw := by decide
    g := ![![![-5, 105, 536], ![16, -1180, 0]], ![![-13, -14, -55], ![3, 118, 0]]]
    h := ![![![6, 2, -1], ![-1, 0, 0]], ![![-9, -1, 4], ![1, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {11} * I3N0 =  Ideal.span {B.equivFun.symm ![18, 5, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 11 ![![5, 0, 0], ![-10, -1, 1]]
  ![5, 2, 1] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![55, 0, 0], ![-110, -11, 11]]
    hsu := by decide
    w := ![![55, 22, 11], ![110, 22, 11]]
    hw := by decide
    g := ![![![-1, 0, 0], ![1, 0, 0]], ![![3, -3, -13], ![8, 28, 0]]]
    h := ![![![-24, 21, -5], ![61, 0, -7]], ![![-23, 21, -5], ![61, 0, -7]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {11} * I5N0 =  Ideal.span {B.equivFun.symm ![5, 2, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E11RS0 : RelationCertificate Table 1 ![![11, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![11, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![11, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![11, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {1} * I11N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 11 ![![11, 0, 0], ![5, 1, 0]]
  ![26, 6, 3] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![121, 0, 0], ![55, 11, 0]]
    hsu := by decide
    w := ![![286, 66, 33], ![341, 77, 33]]
    hw := by decide
    g := ![![![-85, 10777, 54327], ![976, -119520, 0]], ![![-45, 5268, 26560], ![485, -58432, 0]]]
    h := ![![![566, 151, 38], ![-1240, -83, 0]], ![![676, 183, 48], ![-1481, -105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {11} * I11N1 =  Ideal.span {B.equivFun.symm ![26, 6, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E23RS1 : RelationCertificate Table 11 ![![23, 0, 0], ![-6, 1, 0]]
  ![977, 228, 103] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![253, 0, 0], ![-66, 11, 0]]
    hsu := by decide
    w := ![![10747, 2508, 1133], ![11792, 2750, 1243]]
    hw := by decide
    g := ![![![-34, 11, 54], ![-2, -116, 0]], ![![14, -4, -13], ![8, 28, 0]]]
    h := ![![![1471, -236, 11], ![5476, -30, 0]], ![![1616, -258, 11], ![6016, -28, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {11} * I23N1 =  Ideal.span {B.equivFun.symm ![977, 228, 103]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 121 ![![23, 0, 0], ![-2, 1, 0]]
  ![-673, 52, 4] ![![121, 0, 0], ![56, 1, 0]] where
    su := ![![2783, 0, 0], ![-242, 121, 0]]
    hsu := by decide
    w := ![![-81433, 6292, 484], ![-37268, 2299, 484]]
    hw := by decide
    g := ![![![-820703, 260519869, 23262012], ![1773327, -562940664, 0]], ![![61798, -19632478, -1752998], ![-133519, 42422562, 0]]]
    h := ![![![-175711, 88426, -1457], ![-2020340, 6703, 0]], ![![-80404, 40463, -667], ![-924492, 3069, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {121} * I23N2 =  Ideal.span {B.equivFun.symm ![-673, 52, 4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS2 


noncomputable def E29RS1 : RelationCertificate Table 11 ![![29, 0, 0], ![-2, 1, 0]]
  ![31, -36, 15] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![319, 0, 0], ![-22, 11, 0]]
    hsu := by decide
    w := ![![341, -396, 165], ![1606, 220, -165]]
    hw := by decide
    g := ![![![111, -38604, -194390], ![-3497, 427610, 0]], ![![-62, -331, -1600], ![-30, 3505, 0]]]
    h := ![![![701, -351, 0], ![10149, 3, 0]], ![![3278, -1642, 15], ![47458, -90, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {11} * I29N1 =  Ideal.span {B.equivFun.symm ![31, -36, 15]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 


noncomputable def E31RS0 : RelationCertificate Table 11 ![![31, 0, 0], ![10, 1, 0]]
  ![31, 8, 4] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![341, 0, 0], ![110, 11, 0]]
    hsu := by decide
    w := ![![341, 88, 44], ![451, 99, 44]]
    hw := by decide
    g := ![![![-906, 110571, 557386], ![9977, -1226250, 0]], ![![-306, 37195, 187500], ![3356, -412500, 0]]]
    h := ![![![1601, 188, 14], ![-4960, -86, 0]], ![![2131, 251, 19], ![-6602, -117, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {11} * I31N0 =  Ideal.span {B.equivFun.symm ![31, 8, 4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 11 ![![31, 0, 0], ![-5, 1, 0]]
  ![16, 2, 1] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![341, 0, 0], ![-55, 11, 0]]
    hsu := by decide
    w := ![![176, 22, 11], ![121, 33, 11]]
    hw := by decide
    g := ![![![3, 60, 304], ![8, -669, 0]], ![![-1, -9, -45], ![1, 99, 0]]]
    h := ![![![926, -186, 1], ![5738, -6, 0]], ![![636, -128, 1], ![3941, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {11} * I31N1 =  Ideal.span {B.equivFun.symm ![16, 2, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
