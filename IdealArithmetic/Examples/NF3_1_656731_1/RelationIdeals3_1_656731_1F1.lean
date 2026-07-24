import IdealArithmetic.Examples.NF3_1_656731_1.PrimesBelow3_1_656731_1F1
import IdealArithmetic.Examples.NF3_1_656731_1.ClassGroupData3_1_656731_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![1, 1, 0]]
  ![-193014448, 59290957, -11417696] ![![2, 0, 0], ![16, 1, 1]] where
    su := ![![74, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-386028896, 118581914, -22835392], ![1056109624, -473241272, 479818994]]
    hw := by decide
    g := ![![![-7873024576455644, 19968152324635773, 8445351143291800], ![-48777444877681345, 0, 0]], ![![-956551772100599, 2426077971206296, 1026087944179175], ![-5926331219111963, 0, 0]]]
    h := ![![![16355564, 23174629, 194100832], ![1068404, -799238720, 0]], ![![-438954707, -459621611, -4078461449], ![-24285819, 16793664790, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![-193014448, 59290957, -11417696]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E47RS0 : RelationCertificate Table 2 ![![47, 0, 0], ![7, 1, 0]]
  ![303610100, 3371401, 12159404] ![![2, 0, 0], ![16, 1, 1]] where
    su := ![![94, 0, 0], ![14, 2, 0]]
    hsu := by decide
    w := ![![607220200, 6742802, 24318808], ![6297428864, 69929024, 252208282]]
    hw := by decide
    g := ![![![660, -4046, -3353], ![1703, 0, 0]], ![![-67, 1262, -881], ![-313, 0, 0]]]
    h := ![![![-14503474975, -106080578598, -136509982079], ![-4417125584, 712886813013, 0]], ![![-150414300969, -1100152625967, -1415733372125], ![-45809632607, 7393288288224, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {2} * I47N0 =  Ideal.span {B.equivFun.symm ![303610100, 3371401, 12159404]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS0 


noncomputable def E73RS0 : RelationCertificate Table 2 ![![73, 0, 0], ![11, 1, 0]]
  ![1621, -442, -61] ![![2, 0, 0], ![16, 1, 1]] where
    su := ![![146, 0, 0], ![22, 2, 0]]
    hsu := by decide
    w := ![![3242, -884, -122], ![-18694, 6194, -2372]]
    hw := by decide
    g := ![![![487237, -1235800, -522671], ![3018765, 0, 0]], ![![96738, -245390, -103786], ![599429, 0, 0]]]
    h := ![![![-59344, -683105, -559105], ![-18293, 4534956, 0]], ![![343173, 3950321, 3233216], ![105830, -26225106, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {2} * I73N0 =  Ideal.span {B.equivFun.symm ![1621, -442, -61]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS0 


noncomputable def E73RS2 : RelationCertificate Table 2 ![![73, 0, 0], ![-34, 1, 0]]
  ![4239632, -1062407, -422080] ![![2, 0, 0], ![16, 1, 1]] where
    su := ![![146, 0, 0], ![-68, 2, 0]]
    hsu := by decide
    w := ![![8479264, -2124814, -844160], ![-65333224, 19914248, -3429878]]
    hw := by decide
    g := ![![![-4116390059420, 10440295585992, 4415629489899], ![-25503157937359, 0, 0]], ![![1720120839521, -4362698808698, -1845164378400], ![10657035122706, 0, 0]]]
    h := ![![![-1662317, 90300395, -23919973], ![2011232, 193970661, 0]], ![![12855256, -698219642, 184891853], ![-15552018, -1499868912, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {2} * I73N2 =  Ideal.span {B.equivFun.symm ![4239632, -1062407, -422080]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS2 
