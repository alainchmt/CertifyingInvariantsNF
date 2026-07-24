import IdealArithmetic.Examples.NF3_1_648324_3.PrimesBelow3_1_648324_3F0
import IdealArithmetic.Examples.NF3_1_648324_3.ClassGroupData3_1_648324_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![-54, -4, 1]]
  ![478, 27, -8] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![4, 0, 0], ![-108, -8, 2]]
    hsu := by decide
    w := ![![956, 54, -16], ![-200, -268, 38]]
    hw := by decide
    g := ![![![23, -153, -32], ![-69, 0, 3]], ![![-100, 825, -75], ![2168, 0, -69]]]
    h := ![![![566, 40, -10], ![20, 1, 0]], ![![-3263, -346, 68], ![-261, -18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![478, 27, -8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![-53, -4, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![2, 0, 0], ![-53, -4, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-53, -4, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![37, 38, -9], ![131, 0, -4]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![37, 38, -9], ![131, 0, -4]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 2 ![![3, 0, 0], ![0, 1, 0]]
  ![-44597232, -11489879, -1551036] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![6, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![-89194464, -22979758, -3102072], ![111930186, 28837312, 3892792]]
    hw := by decide
    g := ![![![-137, 1610, -211], ![445, 0, 0]], ![![308, -3766, 505], ![-50, 0, 0]]]
    h := ![![![-14865744, -3446964, 4653108], ![-1148987, -7755180, 0]], ![![18655031, 4325596, -5839188], ![1441868, 9731980, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![-44597232, -11489879, -1551036]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E17RS1 : RelationCertificate Table 2 ![![17, 0, 0], ![8, 1, 0]]
  ![-8, -1, 0] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![34, 0, 0], ![16, 2, 0]]
    hsu := by decide
    w := ![![-16, -2, 0], ![-2, 4, 0]]
    hw := by decide
    g := ![![![-3313, 15083, -3553], ![55881, 0, -1742]], ![![-1739, 8125, -1914], ![30092, 0, -938]]]
    h := ![![![-40, -13, -2], ![84, 17, 0]], ![![-17, -10, -2], ![36, 17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![-8, -1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-3, 1, 0]]
  ![3729388478, 960826949, 129703471] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![38, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![7458776956, 1921653898, 259406942], ![45893655002, 11823885008, 1596123972]]
    hw := by decide
    g := ![![![2819, -48563, 6411], ![2121, 0, 0]], ![![-1310, 27179, -3282], ![-6689, 0, 0]]]
    h := ![![![20780744702, -6963173470, 108330683], ![130368253620, -964289753, 0]], ![![127863366013, -42844220009, 666555792], ![802152375582, -5933249031, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![3729388478, 960826949, 129703471]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS1 


noncomputable def E31RS0 : RelationCertificate Table 2 ![![31, 0, 0], ![-15, 1, 0]]
  ![58914202, 3093861, -954433] ![![2, 0, 0], ![-53, -3, 1]] where
    su := ![![62, 0, 0], ![-30, 2, 0]]
    hsu := by decide
    w := ![![117828404, 6187722, -1908866], ![-584702546, -61481508, 13626912]]
    hw := by decide
    g := ![![![203064791050, -4576010282304, -1228031328854], ![868782796209, 0, 0]], ![![-1206940661, 27198082768, 7298956003], ![-5163717941, 0, 0]]]
    h := ![![![1795781932, -141071755, 2846473], ![3707355046, -44597548, 0]], ![![-8899970593, 698890845, -14070854], ![-18373782474, 221504965, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {2} * I31N0 =  Ideal.span {B.equivFun.symm ![58914202, 3093861, -954433]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 2 ![![31, 0, 0], ![-9, 1, 0]]
  ![-1106416, 1411607, -180474] ![![2, 0, 0], ![-53, -4, 1]] where
    su := ![![62, 0, 0], ![-18, 2, 0]]
    hsu := by decide
    w := ![![-2212832, 2823214, -360948], ![967512326, 63983274, -17452544]]
    hw := by decide
    g := ![![![92604082553, -1495413758072, -444197552978], ![314720553021, 0, -3198]], ![![17372969566, -280546755977, -83333574138], ![59043031993, 0, 738]]]
    h := ![![![-3258700, 419372, -9316], ![-11101476, 54161, 0]], ![![1402391614, -161599112, 1617108], ![4776709319, -29428310, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {2} * I31N1 =  Ideal.span {B.equivFun.symm ![-1106416, 1411607, -180474]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
