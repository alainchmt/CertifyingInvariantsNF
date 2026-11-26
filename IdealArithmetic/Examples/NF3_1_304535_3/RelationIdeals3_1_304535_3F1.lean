import IdealArithmetic.Examples.NF3_1_304535_3.PrimesBelow3_1_304535_3F1
import IdealArithmetic.Examples.NF3_1_304535_3.ClassGroupData3_1_304535_3

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 9 ![![41, 0, 0], ![20, 1, 0]]
  ![-918, -77, -58] ![![9, 0, 0], ![9, 4, 1]] where
    su := ![![369, 0, 0], ![180, 9, 0]]
    hsu := by decide
    w := ![![-8262, -693, -522], ![-40707, -3420, -2574]]
    hw := by decide
    g := ![![![-148, 52, -31], ![-124, 21, 0]], ![![-90, 28, -20], ![-70, 13, 0]]]
    h := ![![![-41518, -3643, -393], ![85066, 3211, 0]], ![![-204423, -17921, -1931], ![418841, 15777, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {9} * I41N1 =  Ideal.span {B.equivFun.symm ![-918, -77, -58]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 9 ![![43, 0, 0], ![-14, 1, 0]]
  ![-964, -81, -61] ![![9, 0, 0], ![3, 4, 1]] where
    su := ![![387, 0, 0], ![-126, 9, 0]]
    hsu := by decide
    w := ![![-8676, -729, -549], ![-37017, -3105, -2340]]
    hw := by decide
    g := ![![![26, -7, -3], ![11, 0, 0]], ![![-292, 47, -49], ![-76, 26, 0]]]
    h := ![![![-125340, 9777, -297], ![-384904, 2542, 0]], ![![-534811, 41669, -1250], ![-1642340, 10698, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {9} * I43N1 =  Ideal.span {B.equivFun.symm ![-964, -81, -61]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 3 ![![53, 0, 0], ![7, 1, 0]]
  ![1787, 150, 113] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![159, 0, 0], ![21, 3, 0]]
    hsu := by decide
    w := ![![5361, 450, 339], ![11865, 996, 750]]
    hw := by decide
    g := ![![![-26, 9, 74568], ![6, -44744, 0]], ![![-14, 1, 11107], ![2, -6664, 0]]]
    h := ![![![27703, 4038, 61], ![-209496, -624, 0]], ![![61313, 8937, 135], ![-463662, -1381, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {3} * I53N1 =  Ideal.span {B.equivFun.symm ![1787, 150, 113]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![15, 1, 0]]
  ![9, -8, 5] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![177, 0, 0], ![45, 3, 0]]
    hsu := by decide
    w := ![![27, -24, 15], ![516, -18, -45]]
    hw := by decide
    g := ![![![-720, -85, -310], ![212, 156, 0]], ![![-264, -37, -85], ![78, 40, 0]]]
    h := ![![![-9, -1, 0], ![36, 1, 0]], ![![158, -4, -5], ![-610, 56, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![9, -8, 5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 3 ![![61, 0, 0], ![24, 1, 0]]
  ![-13, 2, 0] ![![3, 0, 0], ![6, 1, 1]] where
    su := ![![183, 0, 0], ![72, 3, 0]]
    hsu := by decide
    w := ![![-39, 6, 0], ![132, -15, -3]]
    hw := by decide
    g := ![![![21, -5, -7], ![41, 0, 0]], ![![8, -3, -4], ![22, 0, 0]]]
    h := ![![![-145, -30, -5], ![368, 61, 0]], ![![332, 9, -1], ![-842, 12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {3} * I61N1 =  Ideal.span {B.equivFun.symm ![-13, 2, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E61RS1 


noncomputable def E67RS0 : RelationCertificate Table 3 ![![67, 0, 0], ![2, 1, 0]]
  ![18, -4, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![201, 0, 0], ![6, 3, 0]]
    hsu := by decide
    w := ![![54, -12, 3], ![87, 15, -21]]
    hw := by decide
    g := ![![![2229, 21181, -116379], ![6320, 69832, 0]], ![![124, 1097, -6019], ![325, 3612, 0]]]
    h := ![![![86, 42, -2], ![-2872, 27, 0]], ![![139, 69, -1], ![-4642, 12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {3} * I67N0 =  Ideal.span {B.equivFun.symm ![18, -4, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 3 ![![67, 0, 0], ![29, 1, 0]]
  ![32, 3, 2] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![201, 0, 0], ![87, 3, 0]]
    hsu := by decide
    w := ![![96, 9, 6], ![210, 18, 15]]
    hw := by decide
    g := ![![![1, -2, 1], ![2, 0, 0]], ![![2, -1, 2], ![1, -1, 0]]]
    h := ![![![1402, 54, 1], ![-3238, -13, 0]], ![![3056, 105, 0], ![-7058, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3} * I67N1 =  Ideal.span {B.equivFun.symm ![32, 3, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 9 ![![67, 0, 0], ![-31, 1, 0]]
  ![-73, 11, 0] ![![9, 0, 0], ![3, 1, 1]] where
    su := ![![603, 0, 0], ![-279, 9, 0]]
    hsu := by decide
    w := ![![-657, 99, 0], ![936, -117, -18]]
    hw := by decide
    g := ![![![951, 52, 30], ![335, 0, 0]], ![![-349, -20, -12], ![-112, 0, 0]]]
    h := ![![![-678, 53, -5], ![-1463, 67, 0]], ![![1050, -28, -1], ![2266, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {9} * I67N2 =  Ideal.span {B.equivFun.symm ![-73, 11, 0]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E67RS2 


noncomputable def E71RS1 : RelationCertificate Table 9 ![![71, 0, 0], ![-25, 1, 0]]
  ![-633, -53, -40] ![![9, 0, 0], ![9, 4, 1]] where
    su := ![![639, 0, 0], ![-225, 9, 0]]
    hsu := by decide
    w := ![![-5697, -477, -360], ![-28062, -2358, -1773]]
    hw := by decide
    g := ![![![-1396804, 491759, -362763], ![-1218548, 224172, 0]], ![![489474, -172330, 127121], ![427021, -78556, 0]]]
    h := ![![![-159323, 6994, -125], ![-452452, 1767, 0]], ![![-784808, 34408, -607], ![-2228730, 8580, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {9} * I71N1 =  Ideal.span {B.equivFun.symm ![-633, -53, -40]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 3 ![![73, 0, 0], ![3, 1, 0]]
  ![2, -3, 2] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![219, 0, 0], ![9, 3, 0]]
    hsu := by decide
    w := ![![6, -9, 6], ![210, -12, -15]]
    hw := by decide
    g := ![![![-121, -9, -43741], ![-3, 26240, 0]], ![![-16, -2, -3281], ![2, 1968, 0]]]
    h := ![![![14, 4, -1], ![-340, 15, 0]], ![![526, 175, 0], ![-12776, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {3} * I73N1 =  Ideal.span {B.equivFun.symm ![2, -3, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E73RS1 
