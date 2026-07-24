import IdealArithmetic.Examples.NF3_1_120204_1.PrimesBelow3_1_120204_1F1
import IdealArithmetic.Examples.NF3_1_120204_1.ClassGroupData3_1_120204_1

set_option linter.all false

noncomputable section


noncomputable def E47RS1 : RelationCertificate Table 11 ![![47, 0, 0], ![-19, 1, 0]]
  ![-11, 5, -2] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![517, 0, 0], ![-209, 11, 0]]
    hsu := by decide
    w := ![![-121, 55, -22], ![-154, 11, 11]]
    hw := by decide
    g := ![![![-4175, 260321, 393607], ![22912, -1443228, 0]], ![![1527, -95315, -144116], ![-8383, 528426, 0]]]
    h := ![![![-16, 7, -1], ![-39, 15, 0]], ![![-10, 7, -1], ![-24, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {11} * I47N1 =  Ideal.span {B.equivFun.symm ![-11, 5, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E47RS1 


noncomputable def E53RS0 : RelationCertificate Table 539 ![![53, 0, 0], ![10, 1, 0]]
  ![55, 5, -24] ![![539, 0, 0], ![68, 1, 0]] where
    su := ![![28567, 0, 0], ![5390, 539, 0]]
    hsu := by decide
    w := ![![29645, 2695, -12936], ![2156, 539, -1617]]
    hw := by decide
    g := ![![![1227989, -5330001801, -235147935], ![-9733620, 42248245652, 0]], ![![220108, -955377519, -42149151], ![-1744680, 7572797462, 0]]]
    h := ![![![135, 5, -3], ![-710, 45, 0]], ![![8, -9, -3], ![-42, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {539} * I53N0 =  Ideal.span {B.equivFun.symm ![55, 5, -24]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 539 ![![53, 0, 0], ![-20, 1, 0]]
  ![1661, 200, 118] ![![539, 0, 0], ![68, 1, 0]] where
    su := ![![28567, 0, 0], ![-10780, 539, 0]]
    hsu := by decide
    w := ![![895279, 107800, 63602], ![120736, 14553, 8624]]
    hw := by decide
    g := ![![![-9520747, 41323413635, 1823097955], ![75465923, -327549932577, 0]], ![![3510520, -15237195345, -672231484], ![-27826034, 120777589956, 0]]]
    h := ![![![7857, -406, 5], ![20738, -49, 0]], ![![1088, -45, -1], ![2872, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {539} * I53N1 =  Ideal.span {B.equivFun.symm ![1661, 200, 118]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 49 ![![59, 0, 0], ![5, 1, 0]]
  ![37, -10, -1] ![![49, 0, 0], ![19, 1, 0]] where
    su := ![![2891, 0, 0], ![245, 49, 0]]
    hsu := by decide
    w := ![![1813, -490, -49], ![637, -147, -49]]
    hw := by decide
    g := ![![![861888, -125293767, -19790389], ![-2222767, 323243018, 0]], ![![80811, -11749723, -1855891], ![-208408, 30312886, 0]]]
    h := ![![![33, 3, -2], ![-382, 39, 0]], ![![7, -2, -2], ![-80, 39, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {49} * I59N1 =  Ideal.span {B.equivFun.symm ![37, -10, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E59RS1 


noncomputable def E61RS0 : RelationCertificate Table 5929 ![![61, 0, 0], ![8, 1, 0]]
  ![15301, 1832, 1124] ![![5929, 0, 0], ![607, 1, 0]] where
    su := ![![361669, 0, 0], ![47432, 5929, 0]]
    hsu := by decide
    w := ![![90719629, 10861928, 6664196], ![9361891, 1120581, 687764]]
    hw := by decide
    g := ![![![-992921940, 58105514575111, 287177180614], ![9698573611, -567557834620110, 0]], ![![-130272756, 7623497605147, 37677913442], ![1272466508, -74464116265870, 0]]]
    h := ![![![41921, 5331, 53], ![-317735, -703, 0]], ![![4319, 548, 5], ![-32735, -63, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {5929} * I61N0 =  Ideal.span {B.equivFun.symm ![15301, 1832, 1124]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 11 ![![61, 0, 0], ![15, 1, 0]]
  ![11, 2, -3] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![671, 0, 0], ![165, 11, 0]]
    hsu := by decide
    w := ![![121, 22, -33], ![-176, 33, 0]]
    hw := by decide
    g := ![![![8355, 4180, -3], ![-46012, 8, 0]], ![![2471, 1235, -3], ![-13610, 10, 0]]]
    h := ![![![1016, 68, 0], ![-4131, -1, 0]], ![![-1486, -114, -3], ![6042, 61, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {11} * I61N1 =  Ideal.span {B.equivFun.symm ![11, 2, -3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 7 ![![61, 0, 0], ![-23, 1, 0]]
  ![19, 3, 1] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![427, 0, 0], ![-161, 7, 0]]
    hsu := by decide
    w := ![![133, 21, 7], ![28, 7, 7]]
    hw := by decide
    g := ![![![-59, -1643, 2510], ![-216, -5856, 0]], ![![25, 632, -967], ![90, 2256, 0]]]
    h := ![![![127, 10, -2], ![336, 41, 0]], ![![34, 14, -2], ![90, 41, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {7} * I61N2 =  Ideal.span {B.equivFun.symm ![19, 3, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS2 


noncomputable def E67RS1 : RelationCertificate Table 121 ![![67, 0, 0], ![30, 1, 0]]
  ![451, 58, 34] ![![121, 0, 0], ![2, 1, 0]] where
    su := ![![8107, 0, 0], ![3630, 121, 0]]
    hsu := by decide
    w := ![![54571, 7018, 4114], ![3146, 363, 242]]
    hw := by decide
    g := ![![![-1, 75, 113], ![25, -4553, 0]], ![![-2, 81, 123], ![112, -4959, 0]]]
    h := ![![![943573, 40518, 907], ![-2107298, -20245, 0]], ![![54338, 2311, 50], ![-121354, -1116, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {121} * I67N1 =  Ideal.span {B.equivFun.symm ![451, 58, 34]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 539 ![![71, 0, 0], ![-24, 1, 0]]
  ![-407, -37, -38] ![![539, 0, 0], ![68, 1, 0]] where
    su := ![![38269, 0, 0], ![-12936, 539, 0]]
    hsu := by decide
    w := ![![-219373, -19943, -20482], ![-30184, -2695, -2695]]
    hw := by decide
    g := ![![![14882521, -64595874177, -2849827634], ![-117965864, 512019031577, 0]], ![![-4987062, 21645590033, 954955737], ![39529800, -171573714082, 0]]]
    h := ![![![-649, 30, -1], ![-1903, 11, 0]], ![![-88, 11, -1], ![-258, 22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {539} * I71N1 =  Ideal.span {B.equivFun.symm ![-407, -37, -38]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E71RS1 


noncomputable def E73RS0 : RelationCertificate Table 847 ![![73, 0, 0], ![22, 1, 0]]
  ![275, -80, -1] ![![847, 0, 0], ![-240, 1, 0]] where
    su := ![![61831, 0, 0], ![18634, 847, 0]]
    hsu := by decide
    w := ![![232925, -67760, -847], ![-66066, 19481, 0]]
    hw := by decide
    g := ![![![10027151, 32379459258, -404743763], ![35387488, 114272655746, 0]], ![![6364616, 20552498200, -256906559], ![22461791, 72533285155, 0]]]
    h := ![![![759, 26, -1], ![-2506, 24, 0]], ![![-250, -33, -3], ![826, 73, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {847} * I73N0 =  Ideal.span {B.equivFun.symm ![275, -80, -1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E73RS0 


noncomputable def E73RS1 : RelationCertificate Table 847 ![![73, 0, 0], ![24, 1, 0]]
  ![517, 19, 32] ![![847, 0, 0], ![-240, 1, 0]] where
    su := ![![61831, 0, 0], ![20328, 847, 0]]
    hsu := by decide
    w := ![![437899, 16093, 27104], ![-121968, -4235, -7623]]
    hw := by decide
    g := ![![![955, 2987915, -37349], ![3370, 10544864, 0]], ![![414, 1017358, -12717], ![1461, 3590432, 0]]]
    h := ![![![4533421, 231529, 5330], ![-13789134, -129686, 0]], ![![-1262688, -64491, -1485], ![3840670, 36132, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {847} * I73N1 =  Ideal.span {B.equivFun.symm ![517, 19, 32]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E73RS1 


noncomputable def E73RS2 : RelationCertificate Table 847 ![![73, 0, 0], ![27, 1, 0]]
  ![55, 61, -31] ![![847, 0, 0], ![-240, 1, 0]] where
    su := ![![61831, 0, 0], ![22869, 847, 0]]
    hsu := by decide
    w := ![![46585, 51667, -26257], ![-15246, -14399, 7623]]
    hw := by decide
    g := ![![![-169086215, -546014113152, 6825185221], ![-596733435, -1926977294055, 0]], ![![-65809953, -212514420831, 2656433688], ![-232254293, -749999777909, 0]]]
    h := ![![![754201, 33518, 620], ![-2039134, -15097, 0]], ![![-246258, -10958, -204], ![665808, 4967, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {847} * I73N2 =  Ideal.span {B.equivFun.symm ![55, 61, -31]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E73RS2 


noncomputable def E79RS1 : RelationCertificate Table 11 ![![79, 0, 0], ![16, 1, 0]]
  ![-11, 3, 1] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![869, 0, 0], ![176, 11, 0]]
    hsu := by decide
    w := ![![-121, 33, 11], ![44, -11, 11]]
    hw := by decide
    g := ![![![1, -3, -4], ![6, 16, 0]], ![![0, -1, -1], ![4, 4, 0]]]
    h := ![![![-21, -12, -2], ![103, 53, 0]], ![![-4, -11, -2], ![20, 53, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {11} * I79N1 =  Ideal.span {B.equivFun.symm ![-11, 3, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E79RS1 
