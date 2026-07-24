import IdealArithmetic.Examples.NF3_3_587412_2.PrimesBelow3_3_587412_2F3
import IdealArithmetic.Examples.NF3_3_587412_2.ClassGroupData3_3_587412_2

set_option linter.all false

noncomputable section


noncomputable def E139RS0 : RelationCertificate Table 13 ![![139, 0, 0], ![19, 1, 0]]
  ![-151, -43, -3] ![![13, 0, 0], ![3, 1, 0]] where
    su := ![![1807, 0, 0], ![247, 13, 0]]
    hsu := by decide
    w := ![![-1963, -559, -39], ![-3939, -910, -52]]
    hw := by decide
    g := ![![![403, -17, -14], ![94, 144, 0]], ![![32, -7, -3], ![7, 36, 0]]]
    h := ![![![-459, -43, -1], ![3350, 136, 0]], ![![-877, -65, -1], ![6400, 135, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N0 : Ideal.span {13} * I139N0 =  Ideal.span {B.equivFun.symm ![-151, -43, -3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E139RS0 


noncomputable def E139RS1 : RelationCertificate Table 13 ![![139, 0, 0], ![25, 1, 0]]
  ![-531, -38, 4] ![![13, 0, 0], ![3, 1, 0]] where
    su := ![![1807, 0, 0], ![325, 13, 0]]
    hsu := by decide
    w := ![![-6903, -494, 52], ![3055, 195, -26]]
    hw := by decide
    g := ![![![181, -378, -130], ![14, 1674, 0]], ![![21, -77, -26], ![8, 336, 0]]]
    h := ![![![-130404, -5442, -9], ![725025, 1255, 0]], ![![57690, 2383, 3], ![-320747, -419, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {13} * I139N1 =  Ideal.span {B.equivFun.symm ![-531, -38, 4]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E139RS1 


noncomputable def E139RS2 : RelationCertificate Table 13 ![![139, 0, 0], ![-44, 1, 0]]
  ![1179, 63, -8] ![![13, 0, 0], ![3, 1, 0]] where
    su := ![![1807, 0, 0], ![-572, 13, 0]]
    hsu := by decide
    w := ![![15327, 819, -104], ![-5759, -312, 39]]
    hw := by decide
    g := ![![![15, 9, 3], ![16, -42, 0]], ![![-9, 2, 1], ![5, -12, 0]]]
    h := ![![![813829, -19818, 30], ![2570933, -4178, 0]], ![![-305725, 7477, -12], ![-965803, 1671, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N2 : Ideal.span {13} * I139N2 =  Ideal.span {B.equivFun.symm ![1179, 63, -8]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E139RS2 


noncomputable def E163RS1 : RelationCertificate Table 845 ![![163, 0, 0], ![78, 1, 0]]
  ![-3193, -251, 23] ![![845, 0, 0], ![-283, 1, 0]] where
    su := ![![137735, 0, 0], ![65910, 845, 0]]
    hsu := by decide
    w := ![![-2698085, -212095, 19435], ![930345, 72670, -6760]]
    hw := by decide
    g := ![![![1198, 2836495, -10023], ![3561, 8469405, 0]], ![![500, 1364054, -4820], ![1486, 4072887, 0]]]
    h := ![![![-31333, -492, -1], ![65437, 186, 0]], ![![10665, 141, 0], ![-22273, -8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {845} * I163N1 =  Ideal.span {B.equivFun.symm ![-3193, -251, 23]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 13 ![![167, 0, 0], ![17, 1, 0]]
  ![-233, -19, 2] ![![13, 0, 0], ![3, 1, 0]] where
    su := ![![2171, 0, 0], ![221, 13, 0]]
    hsu := by decide
    w := ![![-3029, -247, 26], ![1625, 130, -13]]
    hw := by decide
    g := ![![![21081, -1249720, -418914], ![-91266, 5445881, 0]], ![![2836, -168357, -56434], ![-12283, 733642, 0]]]
    h := ![![![-1322, -95, -1], ![12973, 169, 0]], ![![678, 40, 0], ![-6653, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {13} * I167N1 =  Ideal.span {B.equivFun.symm ![-233, -19, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E167RS1 
