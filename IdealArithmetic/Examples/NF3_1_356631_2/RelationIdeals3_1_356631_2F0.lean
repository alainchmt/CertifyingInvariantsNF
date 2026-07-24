import IdealArithmetic.Examples.NF3_1_356631_2.PrimesBelow3_1_356631_2F0
import IdealArithmetic.Examples.NF3_1_356631_2.ClassGroupData3_1_356631_2

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![-25, -2, 1]]
  ![1, 0, 0] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![3, 0, 0], ![-25, -2, 1]]
    hsu := by decide
    w := ![![3, 0, 0], ![-25, -2, 1]]
    hw := by decide
    g := ![![![38, -74, 11], ![-177, 0, 12]], ![![-221, 598, -91], ![1426, 0, -96]]]
    h := ![![![38, -74, 11], ![-177, 0, 12]], ![![-221, 598, -91], ![1426, 0, -96]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![-24, -2, 1]]
  ![11790, 3251, 780] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![9, 0, 0], ![-72, -6, 3]]
    hsu := by decide
    w := ![![35370, 9753, 2340], ![24849, 6852, 1644]]
    hw := by decide
    g := ![![![-25, 82, -11], ![226, 0, -16]], ![![311, -841, 125], ![-1835, 0, 136]]]
    h := ![![![20994, -15615, 11904], ![-153540, -19768, 0]], ![![14753, -10970, 8363], ![-107869, -13888, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![11790, 3251, 780]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 3 ![![7, 0, 0], ![-23, 0, 1]]
  ![-69, -7, 3] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![21, 0, 0], ![-69, 0, 3]]
    hsu := by decide
    w := ![![-207, -21, 9], ![-732, 21, 9]]
    hw := by decide
    g := ![![![-424, 1158, -177], ![2762, 0, -186]], ![![1441, -3865, 585], ![-9199, 0, 620]]]
    h := ![![![0, -1, 0], ![3, 0, 0]], ![![-2, 1, -1], ![10, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3} * I7N0 =  Ideal.span {B.equivFun.symm ![-69, -7, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 3 ![![7, 0, 0], ![0, 1, 0]]
  ![-21, -40, 10] ![![3, 0, 0], ![-25, -3, 1]] where
    su := ![![21, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![-63, -120, 30], ![-12705, -897, 459]]
    hw := by decide
    g := ![![![8, -1027, -701], ![793, 0, 0]], ![![10, -1835, -1252], ![1416, 0, 0]]]
    h := ![![![-3, -12, 1], ![44, 1, 0]], ![![-605, -84, 18], ![289, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {3} * I7N1 =  Ideal.span {B.equivFun.symm ![-21, -40, 10]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E13RS1 : RelationCertificate Table 3 ![![13, 0, 0], ![6, 1, 0]]
  ![6, 1, 0] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![39, 0, 0], ![18, 3, 0]]
    hsu := by decide
    w := ![![18, 3, 0], ![39, 0, 0]]
    hw := by decide
    g := ![![![-52, 169, -26], ![403, 0, -27]], ![![-14, 95, -15], ![225, 0, -15]]]
    h := ![![![30, 5, 0], ![-64, 0, 0]], ![![79, 19, 3], ![-169, -13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {3} * I13N1 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 3 ![![19, 0, 0], ![7, 1, 0]]
  ![-12, 1, 0] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![57, 0, 0], ![21, 3, 0]]
    hsu := by decide
    w := ![![-36, 3, 0], ![489, 36, -18]]
    hw := by decide
    g := ![![![-74, 226, -34], ![535, 0, -36]], ![![-27, 95, -14], ![223, 0, -15]]]
    h := ![![![-148, -28, -3], ![400, 19, 0]], ![![1840, 305, 18], ![-4971, -116, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {3} * I19N1 =  Ideal.span {B.equivFun.symm ![-12, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 3 ![![23, 0, 0], ![-8, 1, 0]]
  ![-453, -125, -30] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![69, 0, 0], ![-24, 3, 0]]
    hsu := by decide
    w := ![![-1359, -375, -90], ![-960, -264, -63]]
    hw := by decide
    g := ![![![101, -271, 42], ![-625, 0, 42]], ![![-21, 81, -13], ![178, 0, -12]]]
    h := ![![![-731, 96, -6], ![-2045, 36, 0]], ![![-512, 64, -3], ![-1432, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {3} * I23N1 =  Ideal.span {B.equivFun.symm ![-453, -125, -30]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 3 ![![29, 0, 0], ![3, 1, 0]]
  ![3, 1, 0] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![87, 0, 0], ![9, 3, 0]]
    hsu := by decide
    w := ![![9, 3, 0], ![114, 6, -3]]
    hw := by decide
    g := ![![![-11443, 30767, -4680], ![73321, 0, -4940]], ![![-1804, 4858, -739], ![11577, 0, -780]]]
    h := ![![![-3, -1, 0], ![30, 0, 0]], ![![34, 9, -2], ![-316, 19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {3} * I29N1 =  Ideal.span {B.equivFun.symm ![3, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 
