import IdealArithmetic.Examples.NF3_1_406700_5.PrimesBelow3_1_406700_5F1
import IdealArithmetic.Examples.NF3_1_406700_5.ClassGroupData3_1_406700_5

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 289 ![![43, 0, 0], ![16, 1, 0]]
  ![11, 3, 3] ![![289, 0, 0], ![-83, 14, 1]] where
    su := ![![12427, 0, 0], ![4624, 289, 0]]
    hsu := by decide
    w := ![![3179, 867, 867], ![-289, -2312, -289]]
    hw := by decide
    g := ![![![-10, 915, -108], ![276, 2064, 0]], ![![7, 336, -40], ![139, 762, 0]]]
    h := ![![![23985, 1882, 24], ![-64459, -1029, 0]], ![![-2739, -219, -3], ![7361, 128, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {289} * I43N1 =  Ideal.span {B.equivFun.symm ![11, 3, 3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 289 ![![47, 0, 0], ![20, 1, 0]]
  ![31, -75, -7] ![![289, 0, 0], ![-53, 1, 0]] where
    su := ![![13583, 0, 0], ![5780, 289, 0]]
    hsu := by decide
    w := ![![8959, -21675, -2023], ![-1734, 4335, 289]]
    hw := by decide
    g := ![![![6002225, 9776797710, -184470018], ![32729087, 53311835232, 0]], ![![2613769, 4257417101, -80329555], ![14252427, 23215241408, 0]]]
    h := ![![![62633, 4493, 68], ![-147186, -3203, 0]], ![![-12098, -885, -14], ![28430, 659, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {289} * I47N1 =  Ideal.span {B.equivFun.symm ![31, -75, -7]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 17 ![![53, 0, 0], ![-24, 1, 0]]
  ![5, -17, 3] ![![17, 0, 0], ![-1, 1, 0]] where
    su := ![![901, 0, 0], ![-408, 17, 0]]
    hsu := by decide
    w := ![![85, -289, 51], ![34, -119, -17]]
    hw := by decide
    g := ![![![104, 1, 0], ![-6, 38, 0]], ![![-46, -1, 0], ![12, -17, 0]]]
    h := ![![![2449, -101, 0], ![5408, 3, 0]], ![![1018, -43, 0], ![2248, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {17} * I53N1 =  Ideal.span {B.equivFun.symm ![5, -17, 3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS1 


noncomputable def E59RS0 : RelationCertificate Table 17 ![![59, 0, 0], ![-29, 1, 0]]
  ![15, 1, 1] ![![17, 0, 0], ![-2, 1, 0]] where
    su := ![![1003, 0, 0], ![-493, 17, 0]]
    hsu := by decide
    w := ![![255, 17, 17], ![-17, -34, 0]]
    hw := by decide
    g := ![![![4, -102, 51], ![1, -865, 0]], ![![0, 45, -23], ![16, 390, 0]]]
    h := ![![![7584, -290, 1], ![15429, -58, 0]], ![![28, -1, 0], ![57, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {17} * I59N0 =  Ideal.span {B.equivFun.symm ![15, 1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 17 ![![59, 0, 0], ![-21, 1, 0]]
  ![9, -34, 2] ![![17, 0, 0], ![-1, 1, 0]] where
    su := ![![1003, 0, 0], ![-357, 17, 0]]
    hsu := by decide
    w := ![![153, -578, 34], ![17, -51, -34]]
    hw := by decide
    g := ![![![-1154, -275761, 276710], ![-16153, -4704144, 0]], ![![385, 90921, -91234], ![5328, 1551004, 0]]]
    h := ![![![3804, -181, 0], ![10687, 2, 0]], ![![446, -22, 0], ![1253, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {17} * I59N1 =  Ideal.span {B.equivFun.symm ![9, -34, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 289 ![![59, 0, 0], ![-10, 1, 0]]
  ![381, -6, 8] ![![289, 0, 0], ![172, 31, 1]] where
    su := ![![17051, 0, 0], ![-2890, 289, 0]]
    hsu := by decide
    w := ![![110109, -1734, 2312], ![68782, -867, 1445]]
    hw := by decide
    g := ![![![-141, -25, -1], ![237, 0, 0]], ![![-6, -1, 0], ![10, 0, 0]]]
    h := ![![![519, -50, 0], ![3024, 8, 0]], ![![322, -31, 0], ![1876, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {289} * I59N2 =  Ideal.span {B.equivFun.symm ![381, -6, 8]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E59RS2 


noncomputable def E61RS0 : RelationCertificate Table 289 ![![61, 0, 0], ![18, 1, 0]]
  ![-56, -23, -6] ![![289, 0, 0], ![-53, 1, 0]] where
    su := ![![17629, 0, 0], ![5202, 289, 0]]
    hsu := by decide
    w := ![![-16184, -6647, -1734], ![2890, 1445, 289]]
    hw := by decide
    g := ![![![3438202, 5600296144, -105667189], ![18747937, 30537817614, 0]], ![![1100738, 1792954338, -33829719], ![6002139, 9776788789, 0]]]
    h := ![![![-260, -31, -1], ![878, 55, 0]], ![![22, 1, 0], ![-74, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {289} * I61N0 =  Ideal.span {B.equivFun.symm ![-56, -23, -6]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 289 ![![61, 0, 0], ![-12, 1, 0]]
  ![-30, 85, 16] ![![289, 0, 0], ![84, 1, 0]] where
    su := ![![17629, 0, 0], ![-3468, 289, 0]]
    hsu := by decide
    w := ![![-8670, 24565, 4624], ![-2312, 6358, 1445]]
    hw := by decide
    g := ![![![39, -87086, -1037], ![-175, 299620, 0]], ![![-73, 15619, 186], ![259, -53740, 0]]]
    h := ![![![-109062, 9417, -27], ![-554396, 1663, 0]], ![![-29048, 2518, -8], ![-147660, 493, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {289} * I61N1 =  Ideal.span {B.equivFun.symm ![-30, 85, 16]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 17 ![![61, 0, 0], ![-7, 1, 0]]
  ![-92, 1, -2] ![![17, 0, 0], ![36, -3, 1]] where
    su := ![![1037, 0, 0], ![-119, 17, 0]]
    hsu := by decide
    w := ![![-1564, 17, -34], ![-3247, 51, -68]]
    hw := by decide
    g := ![![![-31, 5, -1], ![14, 0, 0]], ![![-2, 0, 0], ![1, 0, 0]]]
    h := ![![![-11700, 1692, -3], ![-101944, 181, 0]], ![![-24296, 3512, -6], ![-211695, 362, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {17} * I61N2 =  Ideal.span {B.equivFun.symm ![-92, 1, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E61RS2 


noncomputable def E67RS1 : RelationCertificate Table 289 ![![67, 0, 0], ![32, 1, 0]]
  ![2, -14, 1] ![![289, 0, 0], ![172, 31, 1]] where
    su := ![![19363, 0, 0], ![9248, 289, 0]]
    hsu := by decide
    w := ![![578, -4046, 289], ![578, -3179, -289]]
    hw := by decide
    g := ![![![-74, -6, -1], ![62, 0, 0]], ![![-125, -19, -1], ![180, 0, 0]]]
    h := ![![![7510, 330, 3], ![-15724, -200, 0]], ![![7830, 341, 3], ![-16394, -202, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {289} * I67N1 =  Ideal.span {B.equivFun.symm ![2, -14, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 289 ![![71, 0, 0], ![30, 1, 0]]
  ![-25, 0, 2] ![![289, 0, 0], ![-100, 14, 1]] where
    su := ![![20519, 0, 0], ![8670, 289, 0]]
    hsu := by decide
    w := ![![-7225, 0, 578], ![2890, -1734, -289]]
    hw := by decide
    g := ![![![92, -1347, 138], ![-71, -2655, 0]], ![![122, -605, 60], ![204, -1170, 0]]]
    h := ![![![-118145, -5049, -37], ![279609, 2629, 0]], ![![46670, 1976, 14], ![-110452, -995, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {289} * I71N1 =  Ideal.span {B.equivFun.symm ![-25, 0, 2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 17 ![![73, 0, 0], ![-3, 1, 0]]
  ![64, 0, 1] ![![17, 0, 0], ![-1, 1, 0]] where
    su := ![![1241, 0, 0], ![-51, 17, 0]]
    hsu := by decide
    w := ![![1088, 0, 17], ![-51, 17, 0]]
    hw := by decide
    g := ![![![-1900, -551480, 553381], ![-32320, -9407478, 0]], ![![73, 21020, -21093], ![1242, 358581, 0]]]
    h := ![![![3292, -1097, 0], ![80084, 1, 0]], ![![-150, 53, -1], ![-3649, 73, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {17} * I73N1 =  Ideal.span {B.equivFun.symm ![64, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 289 ![![79, 0, 0], ![12, 1, 0]]
  ![-3, -58, 10] ![![289, 0, 0], ![-53, 1, 0]] where
    su := ![![22831, 0, 0], ![3468, 289, 0]]
    hsu := by decide
    w := ![![-867, -16762, 2890], ![289, 2601, -578]]
    hw := by decide
    g := ![![![-5470436, -8910611571, 168126694], ![-29829335, -48588614592, 0]], ![![-990185, -1612961058, 30433580], ![-5399307, -8795304624, 0]]]
    h := ![![![-33, -5, 0], ![217, 10, 0]], ![![-5, -12, -1], ![33, 77, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {289} * I79N1 =  Ideal.span {B.equivFun.symm ![-3, -58, 10]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E79RS1 
