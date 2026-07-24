import IdealArithmetic.Examples.NF3_1_112887_1.PrimesBelow3_1_112887_1F0
import IdealArithmetic.Examples.NF3_1_112887_1.ClassGroupData3_1_112887_1

set_option linter.all false

noncomputable section


noncomputable def E5RS0 : RelationCertificate Table 15 ![![5, 0, 0], ![12, -1, 1]]
  ![-22, 1, -1] ![![15, 0, 0], ![1, 1, 0]] where
    su := ![![75, 0, 0], ![180, -15, 15]]
    hsu := by decide
    w := ![![-330, 15, -15], ![-75, 0, 0]]
    hw := by decide
    g := ![![![-15, 3357, 3372], ![224, -50580, 0]], ![![-36, 7833, 7868], ![527, -118020, 0]]]
    h := ![![![-2, 0, 0], ![-1, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {15} * I5N0 =  Ideal.span {B.equivFun.symm ![-22, 1, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 3 ![![5, 0, 0], ![1, 1, 0]]
  ![25, 2, 1] ![![15, 0, 0], ![1, 1, 0]] where
    su := ![![15, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![375, 30, 15], ![78, 6, 3]]
    hw := by decide
    g := ![![![-275, 61790, 62064], ![4115, -930960, 0]], ![![-28, 6177, 6205], ![418, -93074, 0]]]
    h := ![![![46, 23, 1], ![-105, 0, 0]], ![![8, 3, 0], ![-14, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {3} * I5N1 =  Ideal.span {B.equivFun.symm ![25, 2, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E11RS1 : RelationCertificate Table 13 ![![11, 0, 0], ![3, 1, 0]]
  ![4, -3, 1] ![![13, 0, 0], ![3, 1, 0]] where
    su := ![![143, 0, 0], ![39, 13, 0]]
    hsu := by decide
    w := ![![52, -39, 13], ![65, -26, 0]]
    hw := by decide
    g := ![![![-434, 25939, 8695], ![1897, -113033, 0]], ![![-172, 10205, 3421], ![753, -44472, 0]]]
    h := ![![![2, 0, 0], ![-6, 1, 0]], ![![1, 0, 0], ![-2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {13} * I11N1 =  Ideal.span {B.equivFun.symm ![4, -3, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E13RS1 : RelationCertificate Table 1 ![![13, 0, 0], ![3, 1, 0]]
  ![1, 0, 0] ![![13, 0, 0], ![3, 1, 0]] where
    su := ![![13, 0, 0], ![3, 1, 0]]
    hsu := by decide
    w := ![![13, 0, 0], ![3, 1, 0]]
    hw := by decide
    g := ![![![16, 5, 0], ![-65, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![16, 5, 0], ![-65, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {1} * I13N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 195 ![![17, 0, 0], ![-6, 1, 0]]
  ![-206, 83, 7] ![![195, 0, 0], ![16, 1, 0]] where
    su := ![![3315, 0, 0], ![-1170, 195, 0]]
    hsu := by decide
    w := ![![-40170, 16185, 1365], ![-2925, 975, 195]]
    hw := by decide
    g := ![![![-2673165, 6395675603, 399740167], ![32579122, -77949332613, 0]], ![![1021662, -2444421075, -152780308], ![-12451488, 29792160071, 0]]]
    h := ![![![-334, 67, -1], ![-912, 24, 0]], ![![-21, 4, 0], ![-57, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {195} * I17N1 =  Ideal.span {B.equivFun.symm ![-206, 83, 7]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 13 ![![19, 0, 0], ![-8, 1, 0]]
  ![-124, -11, -5] ![![13, 0, 0], ![3, 1, 0]] where
    su := ![![247, 0, 0], ![-104, 13, 0]]
    hsu := by decide
    w := ![![-1612, -143, -65], ![-637, -52, -26]]
    hw := by decide
    g := ![![![568, -33854, -11348], ![-2461, 147522, 0]], ![![-126, 7359, 2467], ![544, -32070, 0]]]
    h := ![![![-15780, 2209, -30], ![-37462, 565, 0]], ![![-6235, 874, -12], ![-14802, 226, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {13} * I19N0 =  Ideal.span {B.equivFun.symm ![-124, -11, -5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 195 ![![19, 0, 0], ![-7, 1, 0]]
  ![82, -16, 1] ![![195, 0, 0], ![16, 1, 0]] where
    su := ![![3705, 0, 0], ![-1365, 195, 0]]
    hsu := by decide
    w := ![![15990, -3120, 195], ![1365, -195, 0]]
    hw := by decide
    g := ![![![-351, 829594, 51851], ![4281, -10110944, 0]], ![![128, -327464, -20467], ![-1561, 3991065, 0]]]
    h := ![![![142878, -22308, 271], ![387800, -5148, 0]], ![![12180, -1901, 23], ![33059, -437, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {195} * I19N1 =  Ideal.span {B.equivFun.symm ![82, -16, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 15 ![![19, 0, 0], ![-4, 1, 0]]
  ![7, -1, 1] ![![15, 0, 0], ![1, 1, 0]] where
    su := ![![285, 0, 0], ![-60, 15, 0]]
    hsu := by decide
    w := ![![105, -15, 15], ![60, -15, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![3, 1, 0]], ![![-1, -1, 0], ![14, 0, 0]]]
    h := ![![![17, -4, 0], ![79, 1, 0]], ![![12, -3, 0], ![56, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {15} * I19N2 =  Ideal.span {B.equivFun.symm ![7, -1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E19RS2 


noncomputable def E23RS1 : RelationCertificate Table 195 ![![23, 0, 0], ![-7, 1, 0]]
  ![-317, -19, -11] ![![195, 0, 0], ![16, 1, 0]] where
    su := ![![4485, 0, 0], ![-1365, 195, 0]]
    hsu := by decide
    w := ![![-61815, -3705, -2145], ![-5655, -390, -195]]
    hw := by decide
    g := ![![![4, -30176, -1886], ![-50, 367773, 0]], ![![-17, 8287, 518], ![208, -101011, 0]]]
    h := ![![![-1275, 197, -3], ![-4144, 58, 0]], ![![-109, 22, -1], ![-354, 22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {195} * I23N1 =  Ideal.span {B.equivFun.symm ![-317, -19, -11]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 15 ![![29, 0, 0], ![13, 1, 0]]
  ![-8, -1, 1] ![![15, 0, 0], ![1, 1, 0]] where
    su := ![![435, 0, 0], ![195, 15, 0]]
    hsu := by decide
    w := ![![-120, -15, 15], ![45, -30, 0]]
    hw := by decide
    g := ![![![-794, 178320, 179110], ![11849, -2686652, 0]], ![![-368, 82668, 83034], ![5489, -1245511, 0]]]
    h := ![![![-46, -4, 0], ![102, 1, 0]], ![![-12, -1, 0], ![27, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {15} * I29N1 =  Ideal.span {B.equivFun.symm ![-8, -1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E29RS1 
