import IdealArithmetic.Examples.NF3_1_532652_1.PrimesBelow3_1_532652_1F1
import IdealArithmetic.Examples.NF3_1_532652_1.ClassGroupData3_1_532652_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 5 ![![37, 0, 0], ![-3, 1, 0]]
  ![217551, 80521, 8508] ![![5, 0, 0], ![-43, -4, 1]] where
    su := ![![185, 0, 0], ![-15, 5, 0]]
    hsu := by decide
    w := ![![1087755, 402605, 42540], ![1895645, 701625, 74135]]
    hw := by decide
    g := ![![![23, 349, -29], ![-418, 0, 0]], ![![28, -54, 3], ![123, 0, 0]]]
    h := ![![![3211824, -1073123, 2447], ![39539979, -82031, 0]], ![![5597284, -1870146, 4265], ![68906793, -142978, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {5} * I37N1 =  Ideal.span {B.equivFun.symm ![217551, 80521, 8508]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E37RS1 


noncomputable def E41RS0 : RelationCertificate Table 7 ![![41, 0, 0], ![-20, 1, 0]]
  ![435, 161, 17] ![![7, 0, 0], ![-41, -3, 1]] where
    su := ![![287, 0, 0], ![-140, 7, 0]]
    hsu := by decide
    w := ![![3045, 1127, 119], ![8785, 3248, 343]]
    hw := by decide
    g := ![![![5, 5, -2], ![44, 0, 0]], ![![8, -3, 1], ![-24, 0, 0]]]
    h := ![![![62415, -3688, 29], ![127929, -1172, 0]], ![![179995, -10663, 85], ![368927, -3436, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {7} * I41N0 =  Ideal.span {B.equivFun.symm ![435, 161, 17]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 35 ![![41, 0, 0], ![-15, 1, 0]]
  ![-3477, -1287, -136] ![![35, 0, 0], ![-48, 11, 1]] where
    su := ![![1435, 0, 0], ![-525, 35, 0]]
    hsu := by decide
    w := ![![-121695, -45045, -4760], ![-506590, -187495, -19810]]
    hw := by decide
    g := ![![![-83, -88, 2], ![177, 0, 0]], ![![95, 30, -2], ![-48, 0, 0]]]
    h := ![![![-20562, 1449, -11], ![-55971, 315, 0]], ![![-85654, 6039, -46], ![-233156, 1320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {35} * I41N1 =  Ideal.span {B.equivFun.symm ![-3477, -1287, -136]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 5 ![![41, 0, 0], ![-6, 1, 0]]
  ![49, 80, -9] ![![5, 0, 0], ![-43, -4, 1]] where
    su := ![![205, 0, 0], ![-30, 5, 0]]
    hsu := by decide
    w := ![![245, 400, -45], ![25965, 1610, -460]]
    hw := by decide
    g := ![![![-66, 2342, 530], ![-993, 0, 0]], ![![28, 201, 44], ![-80, 0, 0]]]
    h := ![![![71, -5, -1], ![477, 32, 0]], ![![6711, -1103, 0], ![44993, -92, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {5} * I41N2 =  Ideal.span {B.equivFun.symm ![49, 80, -9]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E41RS2 


noncomputable def E43RS1 : RelationCertificate Table 7 ![![43, 0, 0], ![10, 1, 0]]
  ![241, -16, -1] ![![7, 0, 0], ![-41, -3, 1]] where
    su := ![![301, 0, 0], ![70, 7, 0]]
    hsu := by decide
    w := ![![1687, -112, -7], ![-13027, -1141, 266]]
    hw := by decide
    g := ![![![18, 471, 100], ![-267, 0, 0]], ![![19, 214, 45], ![-119, 0, 0]]]
    h := ![![![617, 61, 0], ![-2629, -1, 0]], ![![-4937, -522, -2], ![21043, 124, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {7} * I43N1 =  Ideal.span {B.equivFun.symm ![241, -16, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 35 ![![53, 0, 0], ![-15, 1, 0]]
  ![117, 16, -3] ![![35, 0, 0], ![-48, 11, 1]] where
    su := ![![1855, 0, 0], ![-525, 35, 0]]
    hsu := by decide
    w := ![![4095, 560, -105], ![-9730, -1295, 245]]
    hw := by decide
    g := ![![![29, -21, -2], ![39, 0, 0]], ![![7, 0, 0], ![3, 0, 0]]]
    h := ![![![65349, -4657, 20], ![230892, -1063, 0]], ![![-155266, 11072, -48], ![-548588, 2551, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {35} * I53N1 =  Ideal.span {B.equivFun.symm ![117, 16, -3]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 5 ![![61, 0, 0], ![-1, 1, 0]]
  ![-1, 1, 0] ![![5, 0, 0], ![-43, -4, 1]] where
    su := ![![305, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![-5, 5, 0], ![285, 25, -5]]
    hw := by decide
    g := ![![![39, 5, -1], ![6, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![2, 0, -1], ![65, 60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {5} * I61N1 =  Ideal.span {B.equivFun.symm ![-1, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS1 


noncomputable def E71RS1 : RelationCertificate Table 5 ![![71, 0, 0], ![-33, 1, 0]]
  ![-27, -300, 32] ![![5, 0, 0], ![-43, -4, 1]] where
    su := ![![355, 0, 0], ![-165, 5, 0]]
    hsu := by decide
    w := ![![-135, -1500, 160], ![-102415, -6640, 1845]]
    hw := by decide
    g := ![![![1381, -35764, -8110], ![15222, 0, 0]], ![![-441, 11857, 2688], ![-5044, 0, 0]]]
    h := ![![![-441, 24, 0], ![-948, 32, 0]], ![![-389959, 13248, -39], ![-838382, 3138, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {5} * I71N1 =  Ideal.span {B.equivFun.symm ![-27, -300, 32]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 5 ![![73, 0, 0], ![-14, 1, 0]]
  ![-29, -10, -1] ![![5, 0, 0], ![-43, -4, 1]] where
    su := ![![365, 0, 0], ![-70, 5, 0]]
    hsu := by decide
    w := ![![-145, -50, -5], ![-205, -80, -10]]
    hw := by decide
    g := ![![![17, 8, -1], ![-2, 0, 0]], ![![6, -1, 0], ![2, 0, 0]]]
    h := ![![![-2119, 165, -1], ![-11047, 72, 0]], ![![-2991, 227, -1], ![-15593, 71, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {5} * I73N1 =  Ideal.span {B.equivFun.symm ![-29, -10, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E73RS1 


noncomputable def E79RS0 : RelationCertificate Table 5 ![![79, 0, 0], ![9, 1, 0]]
  ![9, 1, 0] ![![5, 0, 0], ![-43, -4, 1]] where
    su := ![![395, 0, 0], ![45, 5, 0]]
    hsu := by decide
    w := ![![45, 5, 0], ![-145, -15, 5]]
    hw := by decide
    g := ![![![12, -1, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![315, 35, 0], ![-2764, 0, 0]], ![![-1043, -125, -1], ![9152, 80, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {5} * I79N0 =  Ideal.span {B.equivFun.symm ![9, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 35 ![![79, 0, 0], ![11, 1, 0]]
  ![-2377, -880, -93] ![![35, 0, 0], ![-48, 11, 1]] where
    su := ![![2765, 0, 0], ![385, 35, 0]]
    hsu := by decide
    w := ![![-83195, -30800, -3255], ![-346430, -128205, -13545]]
    hw := by decide
    g := ![![![-27, -66, 3], ![92, 0, 0]], ![![11, -6, 0], ![11, 0, 0]]]
    h := ![![![-10489, -993, -4], ![75114, 223, 0]], ![![-43636, -4091, -13], ![312486, 640, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {35} * I79N1 =  Ideal.span {B.equivFun.symm ![-2377, -880, -93]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 7 ![![79, 0, 0], ![-20, 1, 0]]
  ![-23, -7, 1] ![![7, 0, 0], ![-41, -3, 1]] where
    su := ![![553, 0, 0], ![-140, 7, 0]]
    hsu := by decide
    w := ![![-161, -49, 7], ![-1477, -42, 21]]
    hw := by decide
    g := ![![![40, 12, 1], ![1, 0, 0]], ![![30, 1, -1], ![6, 0, 0]]]
    h := ![![![-17, 1, 0], ![-66, 1, 0]], ![![-309, 16, 0], ![-1210, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {7} * I79N2 =  Ideal.span {B.equivFun.symm ![-23, -7, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E79RS2 
