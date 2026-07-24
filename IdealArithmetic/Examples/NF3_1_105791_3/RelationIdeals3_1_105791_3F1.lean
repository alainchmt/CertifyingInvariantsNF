import IdealArithmetic.Examples.NF3_1_105791_3.PrimesBelow3_1_105791_3F1
import IdealArithmetic.Examples.NF3_1_105791_3.ClassGroupData3_1_105791_3

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 3 ![![37, 0, 0], ![-6, 1, 0]]
  ![-6, 1, 0] ![![3, 0, 0], ![-4, 0, 1]] where
    su := ![![111, 0, 0], ![-18, 3, 0]]
    hsu := by decide
    w := ![![-18, 3, 0], ![87, 3, -6]]
    hw := by decide
    g := ![![![-3, -2, -2], ![5, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-102, 23, -1], ![-628, 37, 0]], ![![527, -88, 0], ![3245, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {3} * I37N1 =  Ideal.span {B.equivFun.symm ![-6, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 9 ![![41, 0, 0], ![-14, 1, 0]]
  ![-18, -1, 1] ![![9, 0, 0], ![4, -3, -1]] where
    su := ![![369, 0, 0], ![-126, 9, 0]]
    hsu := by decide
    w := ![![-162, -9, 9], ![-198, -27, 18]]
    hw := by decide
    g := ![![![-484689, -87277, -47034], ![-181088, -80738, 0]], ![![159346, 28696, 15464], ![59543, 26544, 0]]]
    h := ![![![-10, 1, 0], ![-28, 1, 0]], ![![-34, 3, 0], ![-98, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {9} * I41N1 =  Ideal.span {B.equivFun.symm ![-18, -1, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 9 ![![43, 0, 0], ![14, 1, 0]]
  ![-9, -2, 1] ![![9, 0, 0], ![22, 6, -4]] where
    su := ![![387, 0, 0], ![126, 9, 0]]
    hsu := by decide
    w := ![![-81, -18, 9], ![684, -252, 18]]
    hw := by decide
    g := ![![![-807090, 750067, -469110], ![-1264298, -139200, 0]], ![![-269046, 250018, -156367], ![-421426, -46400, 0]]]
    h := ![![![-527, -52, -1], ![1618, 44, 0]], ![![4248, 358, 4], ![-13042, -170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {9} * I43N1 =  Ideal.span {B.equivFun.symm ![-9, -2, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 3 ![![53, 0, 0], ![-26, 1, 0]]
  ![-15, -4, -1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![159, 0, 0], ![-78, 3, 0]]
    hsu := by decide
    w := ![![-45, -12, -3], ![-48, -18, -3]]
    hw := by decide
    g := ![![![695, 7066, -7774], ![2125, 23324, 0]], ![![-325, -3317, 3649], ![-997, -10948, 0]]]
    h := ![![![-1185, 71, -1], ![-2415, 52, 0]], ![![-1212, 72, -1], ![-2470, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {3} * I53N1 =  Ideal.span {B.equivFun.symm ![-15, -4, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![29, 1, 0]]
  ![12, 5, 1] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![177, 0, 0], ![87, 3, 0]]
    hsu := by decide
    w := ![![36, 15, 3], ![75, 24, 6]]
    hw := by decide
    g := ![![![-15, 18, 19], ![2, -55, 0]], ![![-7, 9, 10], ![2, -29, 0]]]
    h := ![![![244, 8, 0], ![-496, 1, 0]], ![![460, 15, 0], ![-935, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![12, 5, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 9 ![![61, 0, 0], ![-22, 1, 0]]
  ![-45, 5, 1] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![549, 0, 0], ![-198, 9, 0]]
    hsu := by decide
    w := ![![-405, 45, 9], ![-117, -18, 9]]
    hw := by decide
    g := ![![![-4134, 99941, 25243], ![9275, -227194, 0]], ![![719, -17381, -4390], ![-1610, 39512, 0]]]
    h := ![![![-519, 46, -1], ![-1437, 62, 0]], ![![-147, 29, -1], ![-407, 62, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {9} * I61N1 =  Ideal.span {B.equivFun.symm ![-45, 5, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 9 ![![67, 0, 0], ![-9, 1, 0]]
  ![-9, 1, 0] ![![9, 0, 0], ![-7, 0, 1]] where
    su := ![![603, 0, 0], ![-81, 9, 0]]
    hsu := by decide
    w := ![![-81, 9, 0], ![126, 0, -9]]
    hw := by decide
    g := ![![![-2, -1, -1], ![8, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-18, 11, -1], ![-133, 67, 0]], ![![44, 4, -1], ![326, 66, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {9} * I67N1 =  Ideal.span {B.equivFun.symm ![-9, 1, 0]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 9 ![![71, 0, 0], ![16, 1, 0]]
  ![-27, 1, 1] ![![9, 0, 0], ![22, 6, -4]] where
    su := ![![639, 0, 0], ![144, 9, 0]]
    hsu := by decide
    w := ![![-243, 9, 9], ![-468, -378, 108]]
    hw := by decide
    g := ![![![-366608, 340696, -213083], ![-574277, -63228, 0]], ![![-88889, 82589, -51654], ![-139213, -15328, 0]]]
    h := ![![![-2829, -193, -1], ![12552, 72, 0]], ![![-5452, -376, -2], ![24190, 154, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {9} * I71N1 =  Ideal.span {B.equivFun.symm ![-27, 1, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 3 ![![73, 0, 0], ![19, 1, 0]]
  ![-15, -1, 1] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![219, 0, 0], ![57, 3, 0]]
    hsu := by decide
    w := ![![-45, -3, 3], ![48, -9, 0]]
    hw := by decide
    g := ![![![5, 64, 68], ![25, -201, 0]], ![![2, 17, 18], ![7, -53, 0]]]
    h := ![![![-527, -47, -1], ![2024, 74, 0]], ![![514, 27, 0], ![-1974, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {3} * I73N1 =  Ideal.span {B.equivFun.symm ![-15, -1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 3 ![![79, 0, 0], ![6, 1, 0]]
  ![6, 1, 0] ![![3, 0, 0], ![-4, 0, 1]] where
    su := ![![237, 0, 0], ![18, 3, 0]]
    hsu := by decide
    w := ![![18, 3, 0], ![39, 3, 6]]
    hw := by decide
    g := ![![![7, -2, 1], ![-2, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![78, 13, 0], ![-1026, 0, 0]], ![![187, 31, 0], ![-2460, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {3} * I79N1 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS1 
