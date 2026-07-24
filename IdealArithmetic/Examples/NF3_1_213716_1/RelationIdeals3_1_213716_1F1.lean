import IdealArithmetic.Examples.NF3_1_213716_1.PrimesBelow3_1_213716_1F1
import IdealArithmetic.Examples.NF3_1_213716_1.ClassGroupData3_1_213716_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 32 ![![41, 0, 0], ![-10, 1, 0]]
  ![-26, 10, 5] ![![32, 0, 0], ![-3, 1, 0]] where
    su := ![![1312, 0, 0], ![-320, 32, 0]]
    hsu := by decide
    w := ![![-832, 320, 160], ![-352, -96, 0]]
    hw := by decide
    g := ![![![12, -43, 14], ![7, -433, 0]], ![![-3, 12, -4], ![8, 123, 0]]]
    h := ![![![-8686, 920, -5], ![-35610, 210, 0]], ![![-3651, 385, -2], ![-14968, 82, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {32} * I41N1 =  Ideal.span {B.equivFun.symm ![-26, 10, 5]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 16 ![![43, 0, 0], ![0, 1, 0]]
  ![946, -178, 39] ![![16, 0, 0], ![-3, 1, 0]] where
    su := ![![688, 0, 0], ![0, 16, 0]]
    hsu := by decide
    w := ![![15136, -2848, 624], ![-6192, 1168, -256]]
    hw := by decide
    g := ![![![-352, -32055, 10726], ![-1923, -171615, 0]], ![![124, 10732, -3591], ![662, 57457, 0]]]
    h := ![![![22, -5, 0], ![37, 39, 0]], ![![-9, 2, -1], ![-13, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {16} * I43N1 =  Ideal.span {B.equivFun.symm ![946, -178, 39]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 64 ![![47, 0, 0], ![-1, 1, 0]]
  ![-50, 2, 1] ![![64, 0, 0], ![-3, 1, 0]] where
    su := ![![3008, 0, 0], ![-64, 64, 0]]
    hsu := by decide
    w := ![![-3200, 128, 64], ![64, -64, 0]]
    hw := by decide
    g := ![![![923, 1262914, -421074], ![19709, 26948735, 0]], ![![-18, -27063, 9023], ![-385, -577472, 0]]]
    h := ![![![-2, 1, 0], ![-44, 1, 0]], ![![0, 1, -1], ![-1, 47, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {64} * I47N1 =  Ideal.span {B.equivFun.symm ![-50, 2, 1]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 16 ![![53, 0, 0], ![-2, 1, 0]]
  ![18, 30, 7] ![![16, 0, 0], ![-3, 1, 0]] where
    su := ![![848, 0, 0], ![-32, 16, 0]]
    hsu := by decide
    w := ![![288, 480, 112], ![-656, -128, 16]]
    hw := by decide
    g := ![![![9372, 838797, -280652], ![50677, 4490346, 0]], ![![651191, 57520688, -19245916], ![3472946, 307934665, 0]]]
    h := ![![![578, -288, 0], ![15308, 7, 0]], ![![-1317, 660, -1], ![-34880, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {16} * I53N1 =  Ideal.span {B.equivFun.symm ![18, 30, 7]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 8 ![![61, 0, 0], ![29, 1, 0]]
  ![22, -6, 1] ![![8, 0, 0], ![-3, 1, 0]] where
    su := ![![488, 0, 0], ![232, 8, 0]]
    hsu := by decide
    w := ![![176, -48, 8], ![-152, 32, -8]]
    hw := by decide
    g := ![![![-10025, -243948, 82430], ![-26729, -659438, 0]], ![![205665, 5004538, -1691031], ![548443, 13528249, 0]]]
    h := ![![![2366, 110, 1], ![-4976, -60, 0]], ![![-2104, -101, -1], ![4425, 60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {8} * I61N1 =  Ideal.span {B.equivFun.symm ![22, -6, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E61RS1 


noncomputable def E71RS1 : RelationCertificate Table 8 ![![71, 0, 0], ![33, 1, 0]]
  ![22, 10, 1] ![![8, 0, 0], ![-3, 1, 0]] where
    su := ![![568, 0, 0], ![264, 8, 0]]
    hsu := by decide
    w := ![![176, 80, 8], ![-152, -16, 8]]
    hw := by decide
    g := ![![![-23, 160, -54], ![33, 420, 0]], ![![132, 3471, -1173], ![391, 9379, 0]]]
    h := ![![![176, 5, 0], ![-378, 1, 0]], ![![-215, -40, -1], ![462, 72, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {8} * I71N1 =  Ideal.span {B.equivFun.symm ![22, 10, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 32 ![![73, 0, 0], ![-30, 1, 0]]
  ![102, -22, 5] ![![32, 0, 0], ![-3, 1, 0]] where
    su := ![![2336, 0, 0], ![-960, 32, 0]]
    hsu := by decide
    w := ![![3264, -704, 160], ![-736, 128, -32]]
    hw := by decide
    g := ![![![-20841, -7176062, 2394336], ![-222281, -76618750, 0]], ![![1464241, 504186551, -168224877], ![15618562, 5383196063, 0]]]
    h := ![![![113334, -4226, 15], ![275776, -1090, 0]], ![![-25541, 971, -4], ![-62149, 291, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {32} * I73N1 =  Ideal.span {B.equivFun.symm ![102, -22, 5]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 64 ![![79, 0, 0], ![15, 1, 0]]
  ![458, -90, 19] ![![64, 0, 0], ![-3, 1, 0]] where
    su := ![![5056, 0, 0], ![960, 64, 0]]
    hsu := by decide
    w := ![![29312, -5760, 1216], ![-3008, 576, -128]]
    hw := by decide
    g := ![![![-23, -30763, 10257], ![-471, -656439, 0]], ![![-3, -5456, 1819], ![-57, -116414, 0]]]
    h := ![![![319622, 22308, 67], ![-1683312, -5274, 0]], ![![-32828, -2293, -7], ![172891, 551, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {64} * I79N1 =  Ideal.span {B.equivFun.symm ![458, -90, 19]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E79RS1 
