import IdealArithmetic.Examples.NF3_1_557179_1.PrimesBelow3_1_557179_1F1
import IdealArithmetic.Examples.NF3_1_557179_1.ClassGroupData3_1_557179_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 8 ![![41, 0, 0], ![-18, 1, 0]]
  ![7, 0, 1] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![328, 0, 0], ![-144, 8, 0]]
    hsu := by decide
    w := ![![56, 0, 8], ![-144, 8, 0]]
    hw := by decide
    g := ![![![1, -7, -53], ![7, 47, 0]], ![![0, 2, 18], ![1, -16, 0]]]
    h := ![![![491, -14, -7], ![1118, 32, 0]], ![![-1170, 82, -9], ![-2664, 41, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {8} * I41N1 =  Ideal.span {B.equivFun.symm ![7, 0, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E41RS1 


noncomputable def E61RS0 : RelationCertificate Table 48 ![![61, 0, 0], ![6, 1, 0]]
  ![-25, 0, 1] ![![48, 0, 0], ![0, 2, 0]] where
    su := ![![2928, 0, 0], ![288, 48, 0]]
    hsu := by decide
    w := ![![-1200, 0, 48], ![-288, -48, 0]]
    hw := by decide
    g := ![![![-3, -5, -44], ![5, 117, 0]], ![![0, -2, -9], ![23, 24, 0]]]
    h := ![![![-5821, -988, -23], ![59176, 156, 0]], ![![-1398, -240, -9], ![14212, 61, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {48} * I61N0 =  Ideal.span {B.equivFun.symm ![-25, 0, 1]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 48 ![![61, 0, 0], ![22, 1, 0]]
  ![-171, 16, -13] ![![48, 0, 0], ![0, 2, 0]] where
    su := ![![2928, 0, 0], ![1056, 48, 0]]
    hsu := by decide
    w := ![![-8208, 768, -624], ![3744, -336, 288]]
    hw := by decide
    g := ![![![7, -326380, -2942515], ![-13589, 7846705, 0]], ![![4, -122758, -1106737], ![-5105, 2951298, 0]]]
    h := ![![![-1409, -81, -7], ![3899, 46, 0]], ![![618, 20, -3], ![-1710, 21, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {48} * I61N1 =  Ideal.span {B.equivFun.symm ![-171, 16, -13]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 16 ![![61, 0, 0], ![-29, 1, 0]]
  ![-179, 16, -13] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![976, 0, 0], ![-464, 16, 0]]
    hsu := by decide
    w := ![![-2864, 256, -208], ![1872, -176, 144]]
    hw := by decide
    g := ![![![-6, -791991, -7155751], ![-49489, 12721335, 0]], ![![3, 374130, 3380324], ![23388, -6009465, 0]]]
    h := ![![![-253, -41578, 13367], ![-526, -90600, 0]], ![![184, 27182, -8739], ![383, 59232, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {16} * I61N2 =  Ideal.span {B.equivFun.symm ![-179, 16, -13]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E61RS2 


noncomputable def E73RS1 : RelationCertificate Table 32 ![![73, 0, 0], ![-17, 1, 0]]
  ![-163, 16, -13] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![2336, 0, 0], ![-544, 32, 0]]
    hsu := by decide
    w := ![![-5216, 512, -416], ![-736, 96, -64]]
    hw := by decide
    g := ![![![-1062749, 85019317, 45045391], ![2125506, -160161391, 0]], ![![246952, -19757173, -10467851], ![-493905, 37219026, 0]]]
    h := ![![![-104, -34403, 19355], ![-437, -156992, 0]], ![![-8, -4860, 2734], ![-33, -22176, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {32} * I73N1 =  Ideal.span {B.equivFun.symm ![-163, 16, -13]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E73RS1 


noncomputable def E79RS0 : RelationCertificate Table 6 ![![79, 0, 0], ![22, 1, 0]]
  ![-7, 2, 2] ![![6, 0, 0], ![0, 2, 0]] where
    su := ![![474, 0, 0], ![132, 6, 0]]
    hsu := by decide
    w := ![![-42, 12, 12], ![-576, -6, 36]]
    hw := by decide
    g := ![![![-185, 15, -14], ![5, 0, 0]], ![![-26, 2, -2], ![1, 0, 0]]]
    h := ![![![35, -1, -1], ![-126, 9, 0]], ![![964, 36, -3], ![-3466, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {6} * I79N0 =  Ideal.span {B.equivFun.symm ![-7, 2, 2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![-17, 1, 0]]
  ![65, -6, 5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![-34, 2, 0]]
    hsu := by decide
    w := ![![130, -12, 10], ![-720, 64, -54]]
    hw := by decide
    g := ![![![-41, -2, 1], ![-1, 0, 0]], ![![7, -2, -14], ![1, 3, 0]]]
    h := ![![![247, -2, -7], ![1144, 62, 0]], ![![-1198, 86, -9], ![-5546, 76, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![65, -6, 5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 48 ![![79, 0, 0], ![-6, 1, 0]]
  ![23, 0, 1] ![![48, 0, 0], ![0, 2, 0]] where
    su := ![![3792, 0, 0], ![-288, 48, 0]]
    hsu := by decide
    w := ![![1104, 0, 48], ![-288, 48, 0]]
    hw := by decide
    g := ![![![3, -7, -62], ![1, 165, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![5, 302, -545], ![62, 4784, 0]], ![![0, -80, 144], ![1, -1264, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {48} * I79N2 =  Ideal.span {B.equivFun.symm ![23, 0, 1]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E79RS2 
