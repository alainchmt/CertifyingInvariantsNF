import IdealArithmetic.Examples.NF3_1_408807_1.PrimesBelow3_1_408807_1F2
import IdealArithmetic.Examples.NF3_1_408807_1.ClassGroupData3_1_408807_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 275 ![![89, 0, 0], ![-15, 1, 0]]
  ![43, 5, -17] ![![275, 0, 0], ![-80, 1, 0]] where
    su := ![![24475, 0, 0], ![-4125, 275, 0]]
    hsu := by decide
    w := ![![11825, 1375, -4675], ![-5225, 0, 1375]]
    hw := by decide
    g := ![![![60, -8990, 337], ![214, -30900, 0]], ![![105, 43199, -1620], ![360, 148501, 0]]]
    h := ![![![77, -1, -1], ![454, 24, 0]], ![![-11, 11, -2], ![-64, 61, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {275} * I89N1 =  Ideal.span {B.equivFun.symm ![43, 5, -17]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 11 ![![101, 0, 0], ![6, 1, 0]]
  ![-83, -3, -3] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![1111, 0, 0], ![66, 11, 0]]
    hsu := by decide
    w := ![![-913, -33, -33], ![-66, -11, 0]]
    hw := by decide
    g := ![![![-13, -593, 597], ![-47, -2188, 0]], ![![0, -36, 36], ![-1, -132, 0]]]
    h := ![![![-85, -20, -3], ![1417, 100, 0]], ![![-6, -7, -3], ![100, 101, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {11} * I101N1 =  Ideal.span {B.equivFun.symm ![-83, -3, -3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 275 ![![103, 0, 0], ![15, 1, 0]]
  ![-139, 35, -9] ![![275, 0, 0], ![-80, 1, 0]] where
    su := ![![28325, 0, 0], ![4125, 275, 0]]
    hsu := by decide
    w := ![![-38225, 9625, -2475], ![10175, -2750, 825]]
    hw := by decide
    g := ![![![34, -5202, 195], ![122, -17880, 0]], ![![18215, 18619372, -698235], ![62615, 64004874, 0]]]
    h := ![![![-484858, -33118, -159], ![3329349, 5456, 0]], ![![129034, 8812, 42], ![-886031, -1441, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {275} * I103N0 =  Ideal.span {B.equivFun.symm ![-139, 35, -9]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 275 ![![103, 0, 0], ![44, 1, 0]]
  ![-1384, -65, -54] ![![275, 0, 0], ![-80, 1, 0]] where
    su := ![![28325, 0, 0], ![12100, 275, 0]]
    hsu := by decide
    w := ![![-380600, -17875, -14850], ![105050, 4950, 4125]]
    hw := by decide
    g := ![![![-709, -729431, 27354], ![-2439, -2507449, 0]], ![![-245, -314157, 11781], ![-843, -1079925, 0]]]
    h := ![![![-5474232, -183103, -4002], ![12814648, 137384, 0]], ![![1510874, 50528, 1104], ![-3536810, -37899, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {275} * I103N1 =  Ideal.span {B.equivFun.symm ![-1384, -65, -54]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E103RS1 


noncomputable def E109RS1 : RelationCertificate Table 11 ![![109, 0, 0], ![-9, 1, 0]]
  ![37, 2, 2] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![1199, 0, 0], ![-99, 11, 0]]
    hsu := by decide
    w := ![![407, 22, 22], ![99, -11, 0]]
    hw := by decide
    g := ![![![-20, -885, 892], ![-69, -3270, 0]], ![![3, 74, -75], ![10, 275, 0]]]
    h := ![![![3700, -408, -1], ![44807, 37, 0]], ![![900, -100, 0], ![10899, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {11} * I109N1 =  Ideal.span {B.equivFun.symm ![37, 2, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 3025 ![![113, 0, 0], ![25, 1, 0]]
  ![2402, 145, 112] ![![3025, 0, 0], ![-355, 1, 0]] where
    su := ![![341825, 0, 0], ![75625, 3025, 0]]
    hsu := by decide
    w := ![![7266050, 438625, 338800], ![-840950, -51425, -39325]]
    hw := by decide
    g := ![![![1569, 39939153, -337514], ![13370, 340326623, 0]], ![![543, 8985167, -75931], ![4627, 76563760, 0]]]
    h := ![![![111171404, 4785665, 40658], ![-502494650, -1531414, 0]], ![![-12866706, -553884, -4706], ![58157500, 177255, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {3025} * I113N1 =  Ideal.span {B.equivFun.symm ![2402, 145, 112]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E113RS1 


noncomputable def E127RS1 : RelationCertificate Table 55 ![![127, 0, 0], ![-30, 1, 0]]
  ![-1, 5, -6] ![![55, 0, 0], ![-25, 1, 0]] where
    su := ![![6985, 0, 0], ![-1650, 55, 0]]
    hsu := by decide
    w := ![![-55, 275, -330], ![-605, 0, 165]]
    hw := by decide
    g := ![![![-59299, -8659606, 1039437], ![-130443, -19056350, 0]], ![![14040, 2046939, -245700], ![30885, 4504501, 0]]]
    h := ![![![-1963, 95, -3], ![-8310, 125, 0]], ![![-21473, 776, -6], ![-90902, 255, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {55} * I127N1 =  Ideal.span {B.equivFun.symm ![-1, 5, -6]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E127RS1 
