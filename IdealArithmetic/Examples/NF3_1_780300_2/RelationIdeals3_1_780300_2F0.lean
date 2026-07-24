import IdealArithmetic.Examples.NF3_1_780300_2.PrimesBelow3_1_780300_2F0
import IdealArithmetic.Examples.NF3_1_780300_2.ClassGroupData3_1_780300_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 23 ![![2, 0, 0], ![0, 0, 1]]
  ![38, -2, -1] ![![23, 0, 0], ![-4, 1, 0]] where
    su := ![![46, 0, 0], ![0, 0, 23]]
    hsu := by decide
    w := ![![874, -46, -23], ![-322, 46, 0]]
    hw := by decide
    g := ![![![12, 1888, -946], ![81, 10878, 0]], ![![-25, -94, 44], ![5, -518, 0]]]
    h := ![![![19, -3826, 0], ![-1, 0, 90]], ![![-7, 3826, 0], ![0, 0, -90]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {23} * I2N0 =  Ideal.span {B.equivFun.symm ![38, -2, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS0 


noncomputable def E5RS0 : RelationCertificate Table 2783 ![![5, 0, 0], ![0, 1, 0]]
  ![-2045, -287, -86] ![![2783, 0, 0], ![-395, 1, 0]] where
    su := ![![13915, 0, 0], ![0, 2783, 0]]
    hsu := by decide
    w := ![![-5691235, -798721, -239338], ![793155, 111320, 33396]]
    hw := by decide
    g := ![![![-152360, -3054363974, 15465136], ![-1073463, -21519736742, 0]], ![![-168, -6594525, 33390], ![-1184, -46462188, 0]]]
    h := ![![![-409, -112, -16], ![273, -3, 0]], ![![57, 14, 2], ![-30, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2783} * I5N0 =  Ideal.span {B.equivFun.symm ![-2045, -287, -86]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS0 


noncomputable def E11RS0 : RelationCertificate Table 121 ![![11, 0, 0], ![-5, 5, 1]]
  ![-971, -140, -39] ![![121, 0, 0], ![-32, 1, 0]] where
    su := ![![1331, 0, 0], ![-605, 605, 121]]
    hsu := by decide
    w := ![![-117491, -16940, -4719], ![24442, 3509, 968]]
    hw := by decide
    g := ![![![6877, 3363289, -210219], ![26004, 12718249, 0]], ![![-3123, -1532638, 95796], ![-11809, -5795656, 0]]]
    h := ![![![-76, -25, -6], ![27, 0, 0]], ![![17, 4, 1], ![-3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {121} * I11N0 =  Ideal.span {B.equivFun.symm ![-971, -140, -39]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![11, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![11, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![11, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS1 


noncomputable def E17RS0 : RelationCertificate Table 11 ![![17, 0, 0], ![0, 1, 0]]
  ![17, -6, 1] ![![11, 0, 0], ![1, 1, 0]] where
    su := ![![187, 0, 0], ![0, 11, 0]]
    hsu := by decide
    w := ![![187, -66, 11], ![187, 11, -11]]
    hw := by decide
    g := ![![![-11, -1, 1], ![2, -8, 0]], ![![-5, 0, 2], ![5, -12, 0]]]
    h := ![![![1, -2, -1], ![28, 9, 0]], ![![1, 0, -1], ![1, 8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {11} * I17N0 =  Ideal.span {B.equivFun.symm ![17, -6, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS0 


noncomputable def E23RS1 : RelationCertificate Table 1 ![![23, 0, 0], ![-4, 1, 0]]
  ![1, 0, 0] ![![23, 0, 0], ![-4, 1, 0]] where
    su := ![![23, 0, 0], ![-4, 1, 0]]
    hsu := by decide
    w := ![![23, 0, 0], ![-4, 1, 0]]
    hw := by decide
    g := ![![![33, -8, 0], ![184, 0, 0]], ![![-4, 5, -2], ![-22, 23, 0]]]
    h := ![![![33, -8, 0], ![184, 0, 0]], ![![-4, 5, -2], ![-22, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {1} * I23N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 23 ![![29, 0, 0], ![2, 1, 0]]
  ![31, 2, 1] ![![23, 0, 0], ![-4, 1, 0]] where
    su := ![![667, 0, 0], ![46, 23, 0]]
    hsu := by decide
    w := ![![713, 46, 23], ![46, 23, 0]]
    hw := by decide
    g := ![![![1, -146, 73], ![-1, -840, 0]], ![![0, -16, 8], ![1, -92, 0]]]
    h := ![![![1297, 651, 3], ![-18791, -43, 0]], ![![82, 41, 0], ![-1188, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {23} * I29N1 =  Ideal.span {B.equivFun.symm ![31, 2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E29RS1 


noncomputable def E31RS0 : RelationCertificate Table 121 ![![31, 0, 0], ![1, 1, 0]]
  ![691, 101, 29] ![![121, 0, 0], ![-32, 1, 0]] where
    su := ![![3751, 0, 0], ![121, 121, 0]]
    hsu := by decide
    w := ![![83611, 12221, 3509], ![-17182, -2541, -726]]
    hw := by decide
    g := ![![![15, 6480, -405], ![62, 24504, 0]], ![![3, 368, -23], ![11, 1392, 0]]]
    h := ![![![22, 22, 39], ![9, -590, 0]], ![![-5, -5, -8], ![13, 121, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {121} * I31N0 =  Ideal.span {B.equivFun.symm ![691, 101, 29]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 5819 ![![31, 0, 0], ![5, 1, 0]]
  ![-4859, 1482, -225] ![![5819, 0, 0], ![-142, 1, 0]] where
    su := ![![180389, 0, 0], ![29095, 5819, 0]]
    hsu := by decide
    w := ![![-28274521, 8623758, -1309275], ![651728, -215303, 34914]]
    hw := by decide
    g := ![![![-3769493, -899426258158, 12667975841], ![-154469673, -36857475709106, 0]], ![![-1161729, -277207614439, 3904332713], ![-47606383, -11359656028364, 0]]]
    h := ![![![-105123734, -21738652, -285601], ![651766179, 4426703, 0]], ![![2422262, 500905, 6582], ![-15018002, -102018, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {5819} * I31N1 =  Ideal.span {B.equivFun.symm ![-4859, 1482, -225]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 23 ![![31, 0, 0], ![-6, 1, 0]]
  ![199, -25, -1] ![![23, 0, 0], ![-4, 1, 0]] where
    su := ![![713, 0, 0], ![-138, 23, 0]]
    hsu := by decide
    w := ![![4577, -575, -23], ![-966, 299, -46]]
    hw := by decide
    g := ![![![67, 197, -91], ![1, 1078, 0]], ![![4, -36, 18], ![11, -206, 0]]]
    h := ![![![28957, -4985, 53], ![149578, -822, 0]], ![![-6114, 1055, -12], ![-31582, 185, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {23} * I31N2 =  Ideal.span {B.equivFun.symm ![199, -25, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS2 
