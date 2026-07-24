import IdealArithmetic.Examples.NF3_1_466796_1.PrimesBelow3_1_466796_1F1
import IdealArithmetic.Examples.NF3_1_466796_1.ClassGroupData3_1_466796_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 847 ![![37, 0, 0], ![1, 1, 0]]
  ![-951, 254, -16] ![![847, 0, 0], ![-91, 1, 0]] where
    su := ![![31339, 0, 0], ![847, 847, 0]]
    hsu := by decide
    w := ![![-805497, 215138, -13552], ![97405, -26257, 1694]]
    hw := by decide
    g := ![![![152, 723902, -7955], ![1399, 6737873, 0]], ![![71, 26116, -287], ![658, 243087, 0]]]
    h := ![![![-52, -20, -1], ![973, 21, 0]], ![![6, 2, 0], ![-107, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {847} * I37N0 =  Ideal.span {B.equivFun.symm ![-951, 254, -16]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 539 ![![37, 0, 0], ![4, 1, 0]]
  ![-2045, 145, 23] ![![539, 0, 0], ![63, 1, 0]] where
    su := ![![19943, 0, 0], ![2156, 539, 0]]
    hsu := by decide
    w := ![![-1102255, 78155, 12397], ![-144452, 10241, 1617]]
    hw := by decide
    g := ![![![1072123, -5011796152, -79552590], ![-9172603, 42878846008, 0]], ![![173873, -812893485, -12903115], ![-1487579, 6954778984, 0]]]
    h := ![![![-3693041, -935965, -3180], ![34160118, 117683, 0]], ![![-483980, -122661, -417], ![4476748, 15432, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {539} * I37N1 =  Ideal.span {B.equivFun.symm ![-2045, 145, 23]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 121 ![![41, 0, 0], ![12, 1, 0]]
  ![160, -65, 6] ![![121, 0, 0], ![30, 1, 0]] where
    su := ![![4961, 0, 0], ![1452, 121, 0]]
    hsu := by decide
    w := ![![19360, -7865, 726], ![726, -968, 121]]
    hw := by decide
    g := ![![![-11217, 5803579, 193465], ![45294, -23409282, 0]], ![![-33911, 17559551, 585356], ![136799, -70828084, 0]]]
    h := ![![![157256, 14613, 126], ![-537278, -5160, 0]], ![![5790, 530, 4], ![-19782, -163, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {121} * I41N1 =  Ideal.span {B.equivFun.symm ![160, -65, 6]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 121 ![![43, 0, 0], ![-21, 1, 0]]
  ![-348, 96, -7] ![![121, 0, 0], ![30, 1, 0]] where
    su := ![![5203, 0, 0], ![-2541, 121, 0]]
    hsu := by decide
    w := ![![-42108, 11616, -847], ![-5687, 1573, -121]]
    hw := by decide
    g := ![![![-62, 14187, 473], ![227, -57228, 0]], ![![-11, -6900, -230], ![53, 27828, 0]]]
    h := ![![![-920778, 51951, -386], ![-1885386, 16591, 0]], ![![-124346, 7034, -53], ![-254611, 2278, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {121} * I43N1 =  Ideal.span {B.equivFun.symm ![-348, 96, -7]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E43RS1 


noncomputable def E47RS0 : RelationCertificate Table 7 ![![47, 0, 0], ![13, 1, 0]]
  ![-59, 15, -1] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![329, 0, 0], ![91, 7, 0]]
    hsu := by decide
    w := ![![-413, 105, -7], ![679, -196, 14]]
    hw := by decide
    g := ![![![14, -3, 1644], ![2, -11510, 0]], ![![8, -2, 1973], ![5, -13812, 0]]]
    h := ![![![-3454, -304, -3], ![12483, 140, 0]], ![![5672, 474, 3], ![-20499, -139, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {7} * I47N0 =  Ideal.span {B.equivFun.symm ![-59, 15, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 7 ![![47, 0, 0], ![-9, 1, 0]]
  ![-88, 6, 1] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![329, 0, 0], ![-63, 7, 0]]
    hsu := by decide
    w := ![![-616, 42, 7], ![-679, 49, 7]]
    hw := by decide
    g := ![![![16, -2, -9537], ![6, 66758, 0]], ![![-1, 0, 0], ![1, 0, 0]]]
    h := ![![![-422, 56, -1], ![-2194, 48, 0]], ![![-458, 60, -1], ![-2381, 48, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {7} * I47N1 =  Ideal.span {B.equivFun.symm ![-88, 6, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 7 ![![47, 0, 0], ![-5, 1, 0]]
  ![-102, 6, 1] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![329, 0, 0], ![-35, 7, 0]]
    hsu := by decide
    w := ![![-714, 42, 7], ![-679, 35, 7]]
    hw := by decide
    g := ![![![10, -1, -85], ![3, 594, 0]], ![![1, -1, 8], ![6, -56, 0]]]
    h := ![![![-226, 50, -1], ![-2104, 48, 0]], ![![-216, 48, -1], ![-2011, 48, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {7} * I47N2 =  Ideal.span {B.equivFun.symm ![-102, 6, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS2 


noncomputable def E73RS1 : RelationCertificate Table 539 ![![73, 0, 0], ![10, 1, 0]]
  ![783, -128, 2] ![![539, 0, 0], ![63, 1, 0]] where
    su := ![![39347, 0, 0], ![5390, 539, 0]]
    hsu := by decide
    w := ![![422037, -68992, 1078], ![47971, -7007, 0]]
    hw := by decide
    g := ![![![-146, 415102, 6589], ![1209, -3551445, 0]], ![![-24, 59156, 939], ![196, -506115, 0]]]
    h := ![![![2171, 214, 0], ![-15770, 2, 0]], ![![233, 23, 0], ![-1692, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {539} * I73N1 =  Ideal.span {B.equivFun.symm ![783, -128, 2]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 539 ![![79, 0, 0], ![-38, 1, 0]]
  ![142, -101, 10] ![![539, 0, 0], ![63, 1, 0]] where
    su := ![![42581, 0, 0], ![-20482, 539, 0]]
    hsu := by decide
    w := ![![76538, -54439, 5390], ![2156, -4851, 539]]
    hw := by decide
    g := ![![![16356117, -76455928900, -1213590294], ![-139935656, 654125168455, 0]], ![![-7775561, 36346141561, 576924841], ![66524240, -310962489295, 0]]]
    h := ![![![3703046, -111809, 378], ![7698434, -29852, 0]], ![![105616, -3159, 10], ![219570, -789, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {539} * I79N1 =  Ideal.span {B.equivFun.symm ![142, -101, 10]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E79RS1 
