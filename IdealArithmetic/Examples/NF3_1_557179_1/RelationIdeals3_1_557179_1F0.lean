import IdealArithmetic.Examples.NF3_1_557179_1.PrimesBelow3_1_557179_1F0
import IdealArithmetic.Examples.NF3_1_557179_1.ClassGroupData3_1_557179_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 32 ![![2, 0, 0], ![-1, 0, 1]]
  ![1235, -112, 93] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![64, 0, 0], ![-32, 0, 32]]
    hsu := by decide
    w := ![![39520, -3584, 2976], ![6368, -576, 480]]
    hw := by decide
    g := ![![![-12, -182, -96], ![26, 341, 0]], ![![-3, 94, 50], ![8, -176, 0]]]
    h := ![![![523, -56, 141], ![-189, 0, 0]], ![![85, -9, 22], ![-29, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {32} * I2N0 =  Ideal.span {B.equivFun.symm ![1235, -112, 93]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 2 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![6, 0, 0], ![0, 2, 0]] where
    su := ![![6, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![6, 0, 0], ![0, 2, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 96 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, 0, -1] ![![96, 0, 0], ![0, 2, 0]] where
    su := ![![288, 0, 0], ![-96, 96, 0]]
    hsu := by decide
    w := ![![96, 0, -96], ![288, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![5, -5, 0]]]
    h := ![![![25031, 2330, 191], ![-7564, 0, 574]], ![![75091, 6992, 574], ![-22698, 0, 1722]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {96} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, -1]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 16 ![![7, 0, 0], ![2, 1, 0]]
  ![17, 0, -1] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![112, 0, 0], ![32, 16, 0]]
    hsu := by decide
    w := ![![272, 0, -16], ![144, 16, 0]]
    hw := by decide
    g := ![![![1, 8779, 79321], ![550, -141015, 0]], ![![-1, 3667, 33134], ![235, -58905, 0]]]
    h := ![![![293, 162, 50], ![-1017, -39, 0]], ![![157, 87, 27], ![-545, -21, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {16} * I7N0 =  Ideal.span {B.equivFun.symm ![17, 0, -1]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 12 ![![11, 0, 0], ![3, 1, 0]]
  ![67, -6, 5] ![![12, 0, 0], ![0, 2, 0]] where
    su := ![![132, 0, 0], ![36, 12, 0]]
    hsu := by decide
    w := ![![804, -72, 60], ![-1440, 132, -108]]
    hw := by decide
    g := ![![![9, 554, 5128], ![96, -3419, 0]], ![![9, 171, 1578], ![31, -1052, 0]]]
    h := ![![![59, 16, -2], ![-194, 3, 0]], ![![-120, -39, -9], ![400, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {12} * I11N0 =  Ideal.span {B.equivFun.symm ![67, -6, 5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 32 ![![11, 0, 0], ![-3, 1, 0]]
  ![-245, -16, 5] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![352, 0, 0], ![-96, 32, 0]]
    hsu := by decide
    w := ![![-7840, -512, 160], ![-4640, -512, -64]]
    hw := by decide
    g := ![![![-1226, 94646, 50140], ![2359, -178288, 0]], ![![362, -26356, -13956], ![-607, 49637, 0]]]
    h := ![![![-5191, 1724, -11], ![-18952, 14, 0]], ![![-3053, 1014, -10], ![-11146, 12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {32} * I11N1 =  Ideal.span {B.equivFun.symm ![-245, -16, 5]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 96 ![![11, 0, 0], ![-1, 1, 0]]
  ![11457, -1040, 863] ![![96, 0, 0], ![0, 2, 0]] where
    su := ![![1056, 0, 0], ![-96, 96, 0]]
    hsu := by decide
    w := ![![1099872, -99840, 82848], ![-248544, 22560, -18720]]
    hw := by decide
    g := ![![![-10, 5259, 47365], ![119, -252615, 0]], ![![5, -480, -4307], ![30, 22965, 0]]]
    h := ![![![1033, -86, -3452], ![-94, 4315, 0]], ![![-233, 19, 780], ![26, -975, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {96} * I11N2 =  Ideal.span {B.equivFun.symm ![11457, -1040, 863]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 8 ![![13, 0, 0], ![3, 1, 0]]
  ![43, 0, -3] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![104, 0, 0], ![24, 8, 0]]
    hsu := by decide
    w := ![![344, 0, -24], ![432, 40, 0]]
    hw := by decide
    g := ![![![25, 8895, 81336], ![1119, -72297, 0]], ![![-15, 2353, 21501], ![300, -19113, 0]]]
    h := ![![![589, 214, 42], ![-2538, -61, 0]], ![![744, 271, 54], ![-3206, -78, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {8} * I13N0 =  Ideal.span {B.equivFun.symm ![43, 0, -3]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 6 ![![13, 0, 0], ![-3, 1, 0]]
  ![518, -47, 39] ![![6, 0, 0], ![-3, -2, 3]] where
    su := ![![78, 0, 0], ![-18, 6, 0]]
    hsu := by decide
    w := ![![3108, -282, 234], ![31854, -2892, 2400]]
    hw := by decide
    g := ![![![34, -2, 4], ![-11, 0, 0]], ![![8, 3, 1], ![1, 0, 0]]]
    h := ![![![9674, -3261, 210], ![41748, -299, 0]], ![![99095, -33404, 2152], ![427642, -3064, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {6} * I13N1 =  Ideal.span {B.equivFun.symm ![518, -47, 39]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 24 ![![13, 0, 0], ![-1, 1, 0]]
  ![13, 0, -1] ![![24, 0, 0], ![0, 2, 0]] where
    su := ![![312, 0, 0], ![-24, 24, 0]]
    hsu := by decide
    w := ![![312, 0, -24], ![288, 24, 0]]
    hw := by decide
    g := ![![![-3, -307, -2779], ![-17, 3705, 0]], ![![3, 23, 214], ![6, -285, 0]]]
    h := ![![![1, 0, 2], ![0, -3, 0]], ![![1, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {24} * I13N2 =  Ideal.span {B.equivFun.symm ![13, 0, -1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E13RS2 


noncomputable def E19RS1 : RelationCertificate Table 6 ![![19, 0, 0], ![-8, 1, 0]]
  ![11, 1, 0] ![![6, 0, 0], ![0, 2, 0]] where
    su := ![![114, 0, 0], ![-48, 6, 0]]
    hsu := by decide
    w := ![![66, 6, 0], ![0, 24, 18]]
    hw := by decide
    g := ![![![41, -4, 3], ![1, 0, 0]], ![![-40, 3, -3], ![2, 0, 0]]]
    h := ![![![609, -76, 0], ![1445, 0, 0]], ![![0, 5, -6], ![0, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {6} * I19N1 =  Ideal.span {B.equivFun.symm ![11, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 16 ![![23, 0, 0], ![-9, 1, 0]]
  ![-15, 0, -1] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![368, 0, 0], ![-144, 16, 0]]
    hsu := by decide
    w := ![![-240, 0, -16], ![144, -16, 0]]
    hw := by decide
    g := ![![![-1, 116796, 1055272], ![7304, -1876039, 0]], ![![0, -41007, -370503], ![-2561, 658672, 0]]]
    h := ![![![6, -79, 88], ![17, -225, 0]], ![![9, 47, -54], ![22, 138, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {16} * I23N1 =  Ideal.span {B.equivFun.symm ![-15, 0, -1]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 8 ![![29, 0, 0], ![-11, 1, 0]]
  ![-9, 0, 1] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![232, 0, 0], ![-88, 8, 0]]
    hsu := by decide
    w := ![![-72, 0, 8], ![-144, -8, 0]]
    hw := by decide
    g := ![![![1, 12, 116], ![5, -103, 0]], ![![-1, -5, -44], ![2, 39, 0]]]
    h := ![![![-17, 6, -4], ![-44, 13, 0]], ![![-56, 15, -9], ![-146, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {8} * I29N1 =  Ideal.span {B.equivFun.symm ![-9, 0, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 12 ![![31, 0, 0], ![2, 1, 0]]
  ![-2005, 182, -151] ![![12, 0, 0], ![0, 2, 0]] where
    su := ![![372, 0, 0], ![24, 12, 0]]
    hsu := by decide
    w := ![![-24060, 2184, -1812], ![43488, -3948, 3276]]
    hw := by decide
    g := ![![![-35, -5430, -50156], ![-902, 33435, 0]], ![![14, -364, -3346], ![-57, 2229, 0]]]
    h := ![![![-41565, -20942, -598], ![643255, 2043, 0]], ![![75124, 37848, 1074], ![-1162610, -3669, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {12} * I31N1 =  Ideal.span {B.equivFun.symm ![-2005, 182, -151]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E31RS1 
