import IdealArithmetic.Examples.NF3_1_677484_9.PrimesBelow3_1_677484_9F3
import IdealArithmetic.Examples.NF3_1_677484_9.ClassGroupData3_1_677484_9

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 11 ![![139, 0, 0], ![59, 1, 0]]
  ![19, 5, -2] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![1529, 0, 0], ![649, 11, 0]]
    hsu := by decide
    w := ![![209, 55, -22], ![-440, -33, 22]]
    hw := by decide
    g := ![![![-7, 100, 152], ![19, -278, 0]], ![![-3, 42, 64], ![10, -117, 0]]]
    h := ![![![206, -16, -2], ![-485, 46, 0]], ![![-502, -48, -4], ![1182, 93, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {11} * I139N1 =  Ideal.span {B.equivFun.symm ![19, 5, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS1 


noncomputable def E151RS1 : RelationCertificate Table 11 ![![151, 0, 0], ![74, 1, 0]]
  ![-203, -32, 15] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![1661, 0, 0], ![814, 11, 0]]
    hsu := by decide
    w := ![![-2233, -352, 165], ![3058, 209, -132]]
    hw := by decide
    g := ![![![222521, -7617357, -11509461], ![-611564, 21100695, 0]], ![![109248, -3739428, -5650098], ![-300209, 10358523, 0]]]
    h := ![![![-76485, -1516, -39], ![156068, 984, 0]], ![![104482, 1931, 42], ![-213196, -1059, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {11} * I151N1 =  Ideal.span {B.equivFun.symm ![-203, -32, 15]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 121 ![![157, 0, 0], ![-15, 1, 0]]
  ![-1103, -347, 141] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![18997, 0, 0], ![-1815, 121, 0]]
    hsu := by decide
    w := ![![-133463, -41987, 17061], ![68365, 14036, -6171]]
    hw := by decide
    g := ![![![173, 6741, -1377], ![38, 27993, 0]], ![![27, 247, -51], ![102, 1032, 0]]]
    h := ![![![-2564, 178, -3], ![-26763, 102, 0]], ![![1330, -81, -3], ![13883, 70, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {121} * I157N1 =  Ideal.span {B.equivFun.symm ![-1103, -347, 141]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E157RS1 


noncomputable def E167RS1 : RelationCertificate Table 121 ![![167, 0, 0], ![-61, 1, 0]]
  ![-2349287, -462397, -158943] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![20207, 0, 0], ![-7381, 121, 0]]
    hsu := by decide
    w := ![![-284263727, -55950037, -19232103], ![27122029, 5338278, 1834965]]
    hw := by decide
    g := ![![![-8954902, -4780290057, 989089431], ![-37360191, -19946636320, 0]], ![![3231641, 1725076481, -356935437], ![13482342, 7198197760, 0]]]
    h := ![![![-20753358032, 373554612, -3280161], ![-56816531837, 91271324, 0]], ![![1980109160, -35641387, 312963], ![5420950911, -8708276, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {121} * I167N1 =  Ideal.span {B.equivFun.symm ![-2349287, -462397, -158943]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E167RS1 
