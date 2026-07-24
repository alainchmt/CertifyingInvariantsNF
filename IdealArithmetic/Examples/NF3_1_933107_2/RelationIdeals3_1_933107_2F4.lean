import IdealArithmetic.Examples.NF3_1_933107_2.PrimesBelow3_1_933107_2F4
import IdealArithmetic.Examples.NF3_1_933107_2.ClassGroupData3_1_933107_2

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 20 ![![197, 0, 0], ![-87, 1, 0]]
  ![107, -29, 3] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![3940, 0, 0], ![-1740, 20, 0]]
    hsu := by decide
    w := ![![2140, -580, 60], ![-440, 160, -20]]
    hw := by decide
    g := ![![![-249819395, 50463517390, 25294213543], ![2498193946, -505884270855, 0]], ![![111594195, -22542027643, -11298912370], ![-1115941951, 225978247398, 0]]]
    h := ![![![5410, -61, 0], ![12249, 3, 0]], ![![-992, 98, -1], ![-2246, 196, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {20} * I197N1 =  Ideal.span {B.equivFun.symm ![107, -29, 3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E197RS1 


noncomputable def E239RS1 : RelationCertificate Table 20 ![![239, 0, 0], ![-73, 1, 0]]
  ![-91, -3, 1] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![4780, 0, 0], ![-1460, 20, 0]]
    hsu := by decide
    w := ![![-1820, -60, 20], ![-400, -60, 0]]
    hw := by decide
    g := ![![![108049, -21827209, -10940619], ![-1080551, 218812377, 0]], ![![-32241, 6512880, 3264501], ![322430, -65290019, 0]]]
    h := ![![![-142913, 2177, -3], ![-467892, 718, 0]], ![![-31318, 502, -1], ![-102534, 239, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {20} * I239N1 =  Ideal.span {B.equivFun.symm ![-91, -3, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E239RS1 


noncomputable def E241RS0 : RelationCertificate Table 10 ![![241, 0, 0], ![61, 1, 0]]
  ![-148869, 44813, -5201] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![2410, 0, 0], ![610, 10, 0]]
    hsu := by decide
    w := ![![-1488690, 448130, -52010], ![836080, -251680, 29210]]
    hw := by decide
    g := ![![![8880625, -461834364, -233137491], ![-44407306, 2331374905, 0]], ![![2210941, -114979513, -58042529], ![-11055761, 580425284, 0]]]
    h := ![![![-59693472, -1065092, -1443], ![235835703, 342562, 0]], ![![33525018, 598151, 810], ![-132449930, -192289, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N0 : Ideal.span {10} * I241N0 =  Ideal.span {B.equivFun.symm ![-148869, 44813, -5201]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E241RS0 


noncomputable def E241RS1 : RelationCertificate Table 4 ![![241, 0, 0], ![64, 1, 0]]
  ![-145, 43, -5] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![964, 0, 0], ![256, 4, 0]]
    hsu := by decide
    w := ![![-580, 172, -20], ![800, -244, 28]]
    hw := by decide
    g := ![![![-43, -341, -180], ![-103, 724, 0]], ![![-12, -91, -48], ![-28, 193, 0]]]
    h := ![![![-22049, -407, -1], ![83026, 236, 0]], ![![30280, 471, 0], ![-114020, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {4} * I241N1 =  Ideal.span {B.equivFun.symm ![-145, 43, -5]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E241RS1 


noncomputable def E241RS2 : RelationCertificate Table 25 ![![241, 0, 0], ![115, 1, 0]]
  ![19, 2, 1] ![![25, 0, 0], ![-3, 1, 0]] where
    su := ![![6025, 0, 0], ![2875, 25, 0]]
    hsu := by decide
    w := ![![475, 50, 25], ![-275, 50, 0]]
    hw := by decide
    g := ![![![-35231144, -7445516922, 2485753546], ![-293592915, -62143838652, 0]], ![![-16762801, -3542539417, 1182709006], ![-139690032, -29567725151, 0]]]
    h := ![![![19604, 170, 0], ![-41083, 1, 0]], ![![-11616, -216, -1], ![24343, 241, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N2 : Ideal.span {25} * I241N2 =  Ideal.span {B.equivFun.symm ![19, 2, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E241RS2 


noncomputable def E257RS0 : RelationCertificate Table 5 ![![257, 0, 0], ![15, 1, 0]]
  ![-4531, 22, 81] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![1285, 0, 0], ![75, 5, 0]]
    hsu := by decide
    w := ![![-22655, 110, 405], ![-26720, -1490, 265]]
    hw := by decide
    g := ![![![215129, -1308686, -645048], ![-175683, 3250544, 0]], ![![9343, -83459, -42253], ![-12953, 211992, 0]]]
    h := ![![![-30053, -2022, -1], ![514606, 338, 0]], ![![-35432, -2380, -1], ![606712, 310, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N0 : Ideal.span {5} * I257N0 =  Ideal.span {B.equivFun.symm ![-4531, 22, 81]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E257RS0 


noncomputable def E257RS1 : RelationCertificate Table 5 ![![257, 0, 0], ![107, 1, 0]]
  ![-227, 69, -8] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![1285, 0, 0], ![535, 5, 0]]
    hsu := by decide
    w := ![![-1135, 345, -40], ![1290, -385, 45]]
    hw := by decide
    g := ![![![-63291, 918915, 475301], ![158471, -2376510, 0]], ![![-27199, 394885, 204251], ![68101, -1021257, 0]]]
    h := ![![![-38906, -574, -2], ![93445, 506, 0]], ![![44090, 515, 1], ![-105896, -248, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N1 : Ideal.span {5} * I257N1 =  Ideal.span {B.equivFun.symm ![-227, 69, -8]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E257RS1 


noncomputable def E257RS2 : RelationCertificate Table 5 ![![257, 0, 0], ![-123, 1, 0]]
  ![1401, -422, 49] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![1285, 0, 0], ![-615, 5, 0]]
    hsu := by decide
    w := ![![7005, -2110, 245], ![-7880, 2370, -275]]
    hw := by decide
    g := ![![![-77, 517, 278], ![74, -1406, 0]], ![![39, -248, -133], ![-34, 672, 0]]]
    h := ![![![1061595, -9716, 9], ![2218118, -2264, 0]], ![![-1194026, 11159, -12], ![-2494822, 3029, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N2 : Ideal.span {5} * I257N2 =  Ideal.span {B.equivFun.symm ![1401, -422, 49]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E257RS2 
