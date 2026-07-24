import IdealArithmetic.Examples.NF3_3_405405_1.PrimesBelow3_3_405405_1F1
import IdealArithmetic.Examples.NF3_3_405405_1.ClassGroupData3_3_405405_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 4 ![![41, 0, 0], ![12, 1, 0]]
  ![-1097, -17, 23] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![164, 0, 0], ![48, 4, 0]]
    hsu := by decide
    w := ![![-4388, -68, 92], ![1948, 24, -40]]
    hw := by decide
    g := ![![![-40, -38, -28], ![1, 80, 0]], ![![-19, -21, -10], ![0, 25, 0]]]
    h := ![![![-32365, -3014, -26], ![110489, 1089, 0]], ![![14339, 1329, 11], ![-48951, -461, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {4} * I41N1 =  Ideal.span {B.equivFun.symm ![-1097, -17, 23]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS1 


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![-20, 1, 0]]
  ![-21, -19, 3] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![94, 0, 0], ![-40, 2, 0]]
    hsu := by decide
    w := ![![-42, -38, 6], ![90, 104, -16]]
    hw := by decide
    g := ![![![1417, -7179, -8604], ![-2879, 17204, 0]], ![![-602, 3041, 3647], ![1220, -7293, 0]]]
    h := ![![![-823, 62, -1], ![-1933, 50, 0]], ![![1855, -95, 0], ![4357, -8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![-21, -19, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![-21, 1, 0]]
  ![27, -11, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![158, 0, 0], ![-42, 2, 0]]
    hsu := by decide
    w := ![![54, -22, 2], ![64, 64, -10]]
    hw := by decide
    g := ![![![-53, 38, 107], ![-6, -237, 0]], ![![11, -17, -31], ![-3, 66, 0]]]
    h := ![![![1158, -55, 0], ![4355, 1, 0]], ![![1346, -65, 0], ![5062, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![27, -11, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 
