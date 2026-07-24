import IdealArithmetic.Examples.NF3_1_32780_1.PrimesBelow3_1_32780_1F1
import IdealArithmetic.Examples.NF3_1_32780_1.ClassGroupData3_1_32780_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 3 ![![37, 0, 0], ![12, 1, 0]]
  ![-97, 13, 4] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![111, 0, 0], ![36, 3, 0]]
    hsu := by decide
    w := ![![-291, 39, 12], ![207, -144, 69]]
    hw := by decide
    g := ![![![912, 116, 287], ![-265, -74, 0]], ![![430, 64, 114], ![-120, -23, 0]]]
    h := ![![![-1531, 8061, 4027], ![-254, -29799, 0]], ![![1101, -5830, -2911], ![202, 21546, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {3} * I37N1 =  Ideal.span {B.equivFun.symm ![-97, 13, 4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E41RS0 : RelationCertificate Table 3 ![![41, 0, 0], ![18, 1, 0]]
  ![11, 1, -2] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![123, 0, 0], ![54, 3, 0]]
    hsu := by decide
    w := ![![33, 3, -6], ![-81, 12, 3]]
    hw := by decide
    g := ![![![3097, 4285, -7357], ![398, 4416, 0]], ![![2063, 2856, -4905], ![267, 2944, 0]]]
    h := ![![![895, -7996, -2497], ![237, 20475, 0]], ![![-2277, 19919, 6221], ![-483, -51012, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {3} * I41N0 =  Ideal.span {B.equivFun.symm ![11, 1, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS0 


noncomputable def E41RS2 : RelationCertificate Table 27 ![![41, 0, 0], ![-3, 1, 0]]
  ![2891, 280, 451] ![![27, 0, 0], ![11, 1, 0]] where
    su := ![![1107, 0, 0], ![-81, 27, 0]]
    hsu := by decide
    w := ![![78057, 7560, 12177], ![46575, 4509, 7263]]
    hw := by decide
    g := ![![![-49, 162, 89], ![4, -480, 0]], ![![-16, 36, 21], ![21, -112, 0]]]
    h := ![![![19025, 47437, -47414], ![-212, 388885, 0]], ![![11351, 28305, -28291], ![-138, 232040, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {27} * I41N2 =  Ideal.span {B.equivFun.symm ![2891, 280, 451]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E41RS2 


noncomputable def E43RS1 : RelationCertificate Table 27 ![![43, 0, 0], ![-19, 1, 0]]
  ![2131, 206, 332] ![![27, 0, 0], ![11, 1, 0]] where
    su := ![![1161, 0, 0], ![-513, 27, 0]]
    hsu := by decide
    w := ![![57537, 5562, 8964], ![34317, 3321, 5346]]
    hw := by decide
    g := ![![![-1678020, 8257728, 4579851], ![-377785, -24731205, 0]], ![![718834, -3537532, -1961964], ![161869, 10594610, 0]]]
    h := ![![![938297, 10631865, -2530461], ![-167338, 21762031, 0]], ![![559626, 6341126, -1509234], ![-99803, 12979452, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {27} * I43N1 =  Ideal.span {B.equivFun.symm ![2131, 206, 332]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 3 ![![47, 0, 0], ![22, 1, 0]]
  ![257, 25, 40] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![141, 0, 0], ![66, 3, 0]]
    hsu := by decide
    w := ![![771, 75, 120], ![1053, 102, 165]]
    hw := by decide
    g := ![![![-44, -75, 120], ![-7, -69, 0]], ![![-19, -37, 60], ![-5, -35, 0]]]
    h := ![![![18373, -203814, -50930], ![4283, 478750, 0]], ![![25103, -278368, -69560], ![5830, 653875, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {3} * I47N1 =  Ideal.span {B.equivFun.symm ![257, 25, 40]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 
