import IdealArithmetic.Examples.NF3_1_478467_2.PrimesBelow3_1_478467_2F0
import IdealArithmetic.Examples.NF3_1_478467_2.ClassGroupData3_1_478467_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![-119, -7, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-119, -7, 1]] where
    su := ![![2, 0, 0], ![-119, -7, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-119, -7, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![-121, -31, -2] ![![2, 0, 0], ![-119, -7, 1]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-242, -62, -4], ![-1564, -402, -26]]
    hw := by decide
    g := ![![![97, 8, -1], ![3, 0, 0]], ![![75, -4, 0], ![-2, 0, 0]]]
    h := ![![![-82, -45, -9], ![43, 16, 0]], ![![-522, -279, -54], ![262, 95, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![-121, -31, -2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![-119, -6, 1]]
  ![1, 0, 0] ![![5, 0, 0], ![-119, -6, 1]] where
    su := ![![5, 0, 0], ![-119, -6, 1]]
    hsu := by decide
    w := ![![5, 0, 0], ![-119, -6, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![1, 1, 0]]
  ![115033, 29468, 1900] ![![5, 0, 0], ![-119, -6, 1]] where
    su := ![![25, 0, 0], ![5, 5, 0]]
    hsu := by decide
    w := ![![575165, 147340, 9500], ![3276925, 839450, 54125]]
    hw := by decide
    g := ![![![62, -82, -3], ![339, 0, 0]], ![![120, 107, 3], ![-439, 0, 0]]]
    h := ![![![21302, 21302, 17493], ![8523, -85565, 0]], ![![121367, 121367, 99664], ![48550, -487495, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![115033, 29468, 1900]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0], ![-4, 1, 0]]
  ![-7, -1, 0] ![![2, 0, 0], ![-119, -7, 1]] where
    su := ![![22, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![-14, -2, 0], ![-106, -12, 0]]
    hw := by decide
    g := ![![![6, 0, 0], ![-1, 0, 0]], ![![112, 7, -1], ![3, 0, 0]]]
    h := ![![![-9, 6, -1], ![-23, 11, 0]], ![![-83, 23, -1], ![-215, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![-7, -1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS0 


noncomputable def E13RS0 : RelationCertificate Table 5 ![![13, 0, 0], ![-114, -12, 1]]
  ![115061, 10200, -1136] ![![5, 0, 0], ![-119, -6, 1]] where
    su := ![![65, 0, 0], ![-570, -60, 5]]
    hsu := by decide
    w := ![![575305, 51000, -5680], ![2285765, 92010, -15435]]
    hw := by decide
    g := ![![![-19097, 470484, 57262], ![-97078, 0, 0]], ![![87862, -2155884, -262395], ![444856, 0, 0]]]
    h := ![![![143, -132, -11], ![-993, 0, 0]], ![![685, -2214, 65], ![-3932, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {5} * I13N0 =  Ideal.span {B.equivFun.symm ![115061, 10200, -1136]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 5 ![![13, 0, 0], ![-1, 1, 0]]
  ![-233, -16, 2] ![![5, 0, 0], ![-119, -6, 1]] where
    su := ![![65, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![-1165, -80, 10], ![1435, 140, -15]]
    hw := by decide
    g := ![![![52, -2, -1], ![3, 0, 0]], ![![44, -3, -1], ![3, 0, 0]]]
    h := ![![![-38, 19, 0], ![-261, 2, 0]], ![![48, -23, -1], ![337, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {5} * I13N1 =  Ideal.span {B.equivFun.symm ![-233, -16, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 10 ![![19, 0, 0], ![1, 1, 0]]
  ![-194, -3, 1] ![![10, 0, 0], ![-119, -11, 1]] where
    su := ![![190, 0, 0], ![10, 10, 0]]
    hsu := by decide
    w := ![![-1940, -30, 10], ![9940, 910, -100]]
    hw := by decide
    g := ![![![56, 28, 3], ![-7, 0, 0]], ![![2, 20, 3], ![-10, 0, 0]]]
    h := ![![![-11, -11, -10], ![15, 191, 0]], ![![52, 52, 47], ![6, -903, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {10} * I19N1 =  Ideal.span {B.equivFun.symm ![-194, -3, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E29RS0 : RelationCertificate Table 10 ![![29, 0, 0], ![11, 1, 0]]
  ![11, 1, 0] ![![10, 0, 0], ![-119, -11, 1]] where
    su := ![![290, 0, 0], ![110, 10, 0]]
    hsu := by decide
    w := ![![110, 10, 0], ![-370, -60, 0]]
    hw := by decide
    g := ![![![6, 0, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![11, 1, 0], ![-28, 0, 0]], ![![-109, -21, -1], ![284, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {10} * I29N0 =  Ideal.span {B.equivFun.symm ![11, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS0 


noncomputable def E29RS2 : RelationCertificate Table 10 ![![29, 0, 0], ![-4, 1, 0]]
  ![65, 16, 1] ![![10, 0, 0], ![-119, -11, 1]] where
    su := ![![290, 0, 0], ![-40, 10, 0]]
    hsu := by decide
    w := ![![650, 160, 10], ![-3040, -780, -50]]
    hw := by decide
    g := ![![![23, 2, 0], ![11, 0, 0]], ![![110, 10, -1], ![5, 0, 0]]]
    h := ![![![2705, -683, 2], ![19595, -57, 0]], ![![-12616, 3208, -15], ![-91390, 430, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {10} * I29N2 =  Ideal.span {B.equivFun.symm ![65, 16, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS2 
