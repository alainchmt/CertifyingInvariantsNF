import IdealArithmetic.Examples.NF3_1_213716_1.PrimesBelow3_1_213716_1F0
import IdealArithmetic.Examples.NF3_1_213716_1.ClassGroupData3_1_213716_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 8 ![![2, 0, 0], ![0, 1, 0]]
  ![-266, 50, -11] ![![8, 0, 0], ![-3, 1, 0]] where
    su := ![![16, 0, 0], ![0, 8, 0]]
    hsu := by decide
    w := ![![-2128, 400, -88], ![1744, -328, 72]]
    hw := by decide
    g := ![![![2, 3, -1], ![6, 9, 0]], ![![-2, 5, -2], ![9, 18, 0]]]
    h := ![![![-133, 20, 0], ![10, -11, 0]], ![![109, -17, 0], ![-7, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {8} * I2N0 =  Ideal.span {B.equivFun.symm ![-266, 50, -11]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E2RS0 


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


noncomputable def E13RS0 : RelationCertificate Table 64 ![![13, 0, 0], ![3, 1, 0]]
  ![-22, 6, 3] ![![64, 0, 0], ![-3, 1, 0]] where
    su := ![![832, 0, 0], ![192, 64, 0]]
    hsu := by decide
    w := ![![-1408, 384, 192], ![-192, -64, 0]]
    hw := by decide
    g := ![![![563, 770734, -256974], ![12035, 16446333, 0]], ![![120, 162128, -54056], ![2559, 3459584, 0]]]
    h := ![![![-2902, -1039, -24], ![12568, 315, 0]], ![![-411, -149, -4], ![1780, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {64} * I13N0 =  Ideal.span {B.equivFun.symm ![-22, 6, 3]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 16 ![![13, 0, 0], ![4, 1, 0]]
  ![-118, 22, -5] ![![16, 0, 0], ![-3, 1, 0]] where
    su := ![![208, 0, 0], ![64, 16, 0]]
    hsu := by decide
    w := ![![-1888, 352, -80], ![784, -144, 32]]
    hw := by decide
    g := ![![![3, 51, -17], ![11, 273, 0]], ![![1, 15, -5], ![6, 81, 0]]]
    h := ![![![-4190, -1206, -41], ![13588, 528, 0]], ![![1737, 496, 16], ![-5633, -206, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {16} * I13N1 =  Ideal.span {B.equivFun.symm ![-118, 22, -5]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 16 ![![13, 0, 0], ![5, 1, 0]]
  ![-2, 2, 1] ![![16, 0, 0], ![-3, 1, 0]] where
    su := ![![208, 0, 0], ![80, 16, 0]]
    hsu := by decide
    w := ![![-32, 32, 16], ![-80, -16, 0]]
    hw := by decide
    g := ![![![-11, -1202, 402], ![-67, -6431, 0]], ![![-3, -368, 123], ![-17, -1968, 0]]]
    h := ![![![-94, -24, -1], ![244, 14, 0]], ![![-240, -58, -2], ![623, 26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {16} * I13N2 =  Ideal.span {B.equivFun.symm ![-2, 2, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E13RS2 


noncomputable def E19RS1 : RelationCertificate Table 32 ![![19, 0, 0], ![1, 1, 0]]
  ![18, -2, -1] ![![32, 0, 0], ![-3, 1, 0]] where
    su := ![![608, 0, 0], ![32, 32, 0]]
    hsu := by decide
    w := ![![576, -64, -32], ![32, 32, 0]]
    hw := by decide
    g := ![![![1, -3, 1], ![1, -31, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -2, -1], ![18, 18, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {32} * I19N1 =  Ideal.span {B.equivFun.symm ![18, -2, -1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E19RS1 


noncomputable def E29RS1 : RelationCertificate Table 16 ![![29, 0, 0], ![2, 1, 0]]
  ![414, -78, 17] ![![16, 0, 0], ![-3, 1, 0]] where
    su := ![![464, 0, 0], ![32, 16, 0]]
    hsu := by decide
    w := ![![6624, -1248, 272], ![-2704, 512, -112]]
    hw := by decide
    g := ![![![114, 9706, -3247], ![589, 51954, 0]], ![![95662, 8450073, -2827320], ![510198, 45237121, 0]]]
    h := ![![![11938, 5988, 15], ![-172894, -418, 0]], ![![-4877, -2448, -7], ![70632, 196, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {16} * I29N1 =  Ideal.span {B.equivFun.symm ![414, -78, 17]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 4 ![![31, 0, 0], ![-9, 1, 0]]
  ![-6, 2, 1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![124, 0, 0], ![-36, 4, 0]]
    hsu := by decide
    w := ![![-24, 8, 4], ![-92, -12, 4]]
    hw := by decide
    g := ![![![-29, -1, -9], ![-5, 31, 0]], ![![11, -1, 3], ![5, -10, 0]]]
    h := ![![![-6, 1, 0], ![-20, 1, 0]], ![![-62, 16, -1], ![-211, 32, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4} * I31N1 =  Ideal.span {B.equivFun.symm ![-6, 2, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 
