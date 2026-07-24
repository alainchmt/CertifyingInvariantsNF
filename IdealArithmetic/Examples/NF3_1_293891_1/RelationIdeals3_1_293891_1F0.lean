import IdealArithmetic.Examples.NF3_1_293891_1.PrimesBelow3_1_293891_1F0
import IdealArithmetic.Examples.NF3_1_293891_1.ClassGroupData3_1_293891_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 32 ![![2, 0, 0], ![17, 1, 1]]
  ![-27, -1, -1] ![![32, 0, 0], ![-1, 1, 0]] where
    su := ![![64, 0, 0], ![544, 32, 32]]
    hsu := by decide
    w := ![![-864, -32, -32], ![-64, 0, 0]]
    hw := by decide
    g := ![![![1, -1, 0], ![31, 0, 0]], ![![-1, 0, 0], ![5, 0, 0]]]
    h := ![![![-5, 0, 0], ![-1, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {32} * I2N0 =  Ideal.span {B.equivFun.symm ![-27, -1, -1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E7RS0 : RelationCertificate Table 4 ![![7, 0, 0], ![0, 1, 0]]
  ![-21, 5, 1] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![28, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![-84, 20, 4], ![112, -52, 4]]
    hw := by decide
    g := ![![![143, 12, 12], ![-29, -30, 0]], ![![55, -3, 13], ![-14, -45, 0]]]
    h := ![![![-3, 0, 0], ![5, 1, 0]], ![![4, -2, 0], ![1, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4} * I7N0 =  Ideal.span {B.equivFun.symm ![-21, 5, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 32 ![![7, 0, 0], ![3, 1, 0]]
  ![83, -55, 9] ![![32, 0, 0], ![-1, 1, 0]] where
    su := ![![224, 0, 0], ![96, 32, 0]]
    hsu := by decide
    w := ![![2656, -1760, 288], ![736, -96, -64]]
    hw := by decide
    g := ![![![8025, 8371931, -8380115], ![261378, 268163543, 0]], ![![2995, 3189568, -3192693], ![99583, 102166064, 0]]]
    h := ![![![3353, 1507, 135], ![-7796, -936, 0]], ![![1043, 455, 36], ![-2426, -254, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {32} * I7N1 =  Ideal.span {B.equivFun.symm ![83, -55, 9]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 32 ![![7, 0, 0], ![-3, 1, 0]]
  ![5, -1, -1] ![![32, 0, 0], ![-1, 1, 0]] where
    su := ![![224, 0, 0], ![-96, 32, 0]]
    hsu := by decide
    w := ![![160, -32, -32], ![-96, 32, 0]]
    hw := by decide
    g := ![![![-1, -658, 658], ![-4, -21057, 0]], ![![1, 376, -377], ![33, 12064, 0]]]
    h := ![![![587, -217, 7], ![1368, -50, 0]], ![![-351, 132, -5], ![-818, 35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {32} * I7N2 =  Ideal.span {B.equivFun.symm ![5, -1, -1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E7RS2 


noncomputable def E11RS0 : RelationCertificate Table 32 ![![11, 0, 0], ![20, 4, 1]]
  ![-251, 95, -1] ![![32, 0, 0], ![-1, 1, 0]] where
    su := ![![352, 0, 0], ![640, 128, 32]]
    hsu := by decide
    w := ![![-8032, 3040, -32], ![160, -320, 96]]
    hw := by decide
    g := ![![![27, -48, 50], ![29, -1575, 0]], ![![91, -80, 90], ![4, -2793, 0]]]
    h := ![![![-21, 9, 0], ![-1, 0, 0]], ![![-5, -2, 0], ![3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {32} * I11N0 =  Ideal.span {B.equivFun.symm ![-251, 95, -1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![-4, 1, 0]]
  ![-969, -79, -29] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![22, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![-1938, -158, -58], ![-3608, -294, -108]]
    hw := by decide
    g := ![![![43, -229, -281], ![-91, 559, 0]], ![![-25, 74, 87], ![27, -172, 0]]]
    h := ![![![-1607, 406, -11], ![-4177, 92, 0]], ![![-2996, 755, -20], ![-7788, 166, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![-969, -79, -29]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 16 ![![13, 0, 0], ![0, 1, 0]]
  ![2171, 177, 65] ![![16, 0, 0], ![-1, 1, 0]] where
    su := ![![208, 0, 0], ![0, 16, 0]]
    hsu := by decide
    w := ![![34736, 2832, 1040], ![3744, 304, 112]]
    hw := by decide
    g := ![![![-4, 0, 1], ![1, -12, 0]], ![![2, -2, 1], ![4, -15, 0]]]
    h := ![![![167, 13, 0], ![8, 65, 0]], ![![18, 1, 0], ![6, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {16} * I13N0 =  Ideal.span {B.equivFun.symm ![2171, 177, 65]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E13RS0 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![-8, 1, 0]]
  ![-233, -19, -7] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![68, 0, 0], ![-32, 4, 0]]
    hsu := by decide
    w := ![![-932, -76, -28], ![-404, -32, -12]]
    hw := by decide
    g := ![![![8, 9, -12], ![3, 47, 0]], ![![-4, -4, 5], ![3, -20, 0]]]
    h := ![![![-7865, 1145, -21], ![-16684, 350, 0]], ![![-3413, 504, -10], ![-7240, 167, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![-233, -19, -7]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E31RS0 : RelationCertificate Table 8 ![![31, 0, 0], ![9, 1, 0]]
  ![11, -7, 1] ![![8, 0, 0], ![-1, 1, 0]] where
    su := ![![248, 0, 0], ![72, 8, 0]]
    hsu := by decide
    w := ![![88, -56, 8], ![80, -8, -8]]
    hw := by decide
    g := ![![![-31, 58, -64], ![19, 504, 0]], ![![-12, 19, -21], ![5, 165, 0]]]
    h := ![![![14, 1, 0], ![-47, 1, 0]], ![![16, -7, -1], ![-54, 30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {8} * I31N0 =  Ideal.span {B.equivFun.symm ![11, -7, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 8 ![![31, 0, 0], ![-7, 1, 0]]
  ![-1705, -139, -51] ![![8, 0, 0], ![-1, 1, 0]] where
    su := ![![248, 0, 0], ![-56, 8, 0]]
    hsu := by decide
    w := ![![-13640, -1112, -408], ![-2936, -240, -88]]
    hw := by decide
    g := ![![![-13, 17, -13], ![7, 105, 0]], ![![4, -5, 3], ![4, -23, 0]]]
    h := ![![![-4556, 669, -6], ![-19933, 135, 0]], ![![-974, 148, -2], ![-4261, 51, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {8} * I31N1 =  Ideal.span {B.equivFun.symm ![-1705, -139, -51]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E31RS1 
