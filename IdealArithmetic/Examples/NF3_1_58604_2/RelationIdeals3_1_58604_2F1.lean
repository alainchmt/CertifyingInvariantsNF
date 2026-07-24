import IdealArithmetic.Examples.NF3_1_58604_2.PrimesBelow3_1_58604_2F1
import IdealArithmetic.Examples.NF3_1_58604_2.ClassGroupData3_1_58604_2

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 9 ![![37, 0, 0], ![3, 1, 0]]
  ![-37, -6, -2] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![333, 0, 0], ![27, 9, 0]]
    hsu := by decide
    w := ![![-333, -54, -18], ![27, 9, 0]]
    hw := by decide
    g := ![![![-1, -87, 29], ![0, -263, 0]], ![![0, -9, 3], ![1, -27, 0]]]
    h := ![![![-862, -290, -1], ![10619, 35, 0]], ![![66, 22, 0], ![-813, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {9} * I37N0 =  Ideal.span {B.equivFun.symm ![-37, -6, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 9 ![![37, 0, 0], ![8, 1, 0]]
  ![-37, 21, -2] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![333, 0, 0], ![72, 9, 0]]
    hsu := by decide
    w := ![![-333, 189, -18], ![27, -72, 27]]
    hw := by decide
    g := ![![![-91, -60, 10], ![24, -137, 0]], ![![-23, -15, 2], ![13, -31, 0]]]
    h := ![![![-97, -19, -1], ![444, 35, 0]], ![![7, 0, 0], ![-32, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {9} * I37N1 =  Ideal.span {B.equivFun.symm ![-37, 21, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E37RS1 


noncomputable def E37RS2 : RelationCertificate Table 9 ![![37, 0, 0], ![-11, 1, 0]]
  ![-31, 12, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![333, 0, 0], ![-99, 9, 0]]
    hsu := by decide
    w := ![![-279, 108, 9], ![135, -81, 9]]
    hw := by decide
    g := ![![![38, -67, 27], ![-17, -222, 0]], ![![-7, 20, -8], ![10, 67, 0]]]
    h := ![![![-3426, 334, -2], ![-11521, 75, 0]], ![![1684, -153, 0], ![5663, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {9} * I37N2 =  Ideal.span {B.equivFun.symm ![-31, 12, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E37RS2 


noncomputable def E43RS1 : RelationCertificate Table 9 ![![43, 0, 0], ![-6, 1, 0]]
  ![-131, -15, -7] ![![9, 0, 0], ![33, 7, 4]] where
    su := ![![387, 0, 0], ![-54, 9, 0]]
    hsu := by decide
    w := ![![-1179, -135, -63], ![-8901, -1062, -468]]
    hw := by decide
    g := ![![![-233, 467, 90], ![-342, 80, 0]], ![![-5, -59, -14], ![47, -9, 0]]]
    h := ![![![-7253, 1231, -4], ![-51958, 165, 0]], ![![-54755, 9292, -30], ![-392246, 1238, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {9} * I43N1 =  Ideal.span {B.equivFun.symm ![-131, -15, -7]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 9 ![![47, 0, 0], ![22, 1, 0]]
  ![5, 3, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![423, 0, 0], ![198, 9, 0]]
    hsu := by decide
    w := ![![45, 27, 9], ![27, -18, 0]]
    hw := by decide
    g := ![![![-10244, -307408, 103608], ![-30735, -932470, 0]], ![![-4933, -148058, 49901], ![-14801, -449108, 0]]]
    h := ![![![9, 0, 0], ![-19, 1, 0]], ![![-21, -1, 0], ![45, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {9} * I47N1 =  Ideal.span {B.equivFun.symm ![5, 3, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 9 ![![53, 0, 0], ![-18, 1, 0]]
  ![-169, -20, -9] ![![9, 0, 0], ![6, 1, 1]] where
    su := ![![477, 0, 0], ![-162, 9, 0]]
    hsu := by decide
    w := ![![-1521, -180, -81], ![-2232, -261, -117]]
    hw := by decide
    g := ![![![3, -4, -3], ![14, 0, 0]], ![![-8, 1, 0], ![4, 0, 0]]]
    h := ![![![-263, 29, -1], ![-765, 44, 0]], ![![-400, 35, -1], ![-1164, 40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {9} * I53N1 =  Ideal.span {B.equivFun.symm ![-169, -20, -9]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![-28, 1, 0]]
  ![17, 3, 1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![177, 0, 0], ![-84, 3, 0]]
    hsu := by decide
    w := ![![51, 9, 3], ![42, 3, 3]]
    hw := by decide
    g := ![![![1, -1, 0], ![0, 2, 0]], ![![0, 0, -1], ![1, 2, 0]]]
    h := ![![![239, -8, 0], ![503, 1, 0]], ![![210, -7, 0], ![442, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![17, 3, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 9 ![![61, 0, 0], ![-10, 1, 0]]
  ![-661, -78, -35] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![549, 0, 0], ![-90, 9, 0]]
    hsu := by decide
    w := ![![-5949, -702, -315], ![513, 63, 27]]
    hw := by decide
    g := ![![![-1, -148, 49], ![-12, -452, 0]], ![![1, 24, -8], ![7, 74, 0]]]
    h := ![![![-60651, 6217, -16], ![-369905, 941, 0]], ![![5247, -534, 1], ![32001, -58, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {9} * I61N1 =  Ideal.span {B.equivFun.symm ![-661, -78, -35]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E61RS1 
