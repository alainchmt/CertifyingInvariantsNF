import IdealArithmetic.Examples.NF3_1_672300_4.PrimesBelow3_1_672300_4F1
import IdealArithmetic.Examples.NF3_1_672300_4.ClassGroupData3_1_672300_4

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 49 ![![37, 0, 0], ![15, 1, 0]]
  ![-159, 19, 0] ![![49, 0, 0], ![-18, 4, 1]] where
    su := ![![1813, 0, 0], ![735, 49, 0]]
    hsu := by decide
    w := ![![-7791, 931, 0], ![5978, -1225, 392]]
    hw := by decide
    g := ![![![-5869, -17, 198], ![2182, 0, 501]], ![![-2387, -7, 83], ![922, 0, 207]]]
    h := ![![![-62963, -554537, -277816], ![-40496, 1468456, 0]], ![![49101, 432592, 216724], ![31631, -1145540, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {49} * I37N0 =  Ideal.span {B.equivFun.symm ![-159, 19, 0]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E37RS0 


noncomputable def E37RS2 : RelationCertificate Table 49 ![![37, 0, 0], ![-2, 1, 0]]
  ![17, 0, -2] ![![49, 0, 0], ![-11, 4, 1]] where
    su := ![![1813, 0, 0], ![-98, 49, 0]]
    hsu := by decide
    w := ![![833, 0, -98], ![-1519, 98, 49]]
    hw := by decide
    g := ![![![5531152, -746944, 1055071], ![-1281119, -1738530, 0]], ![![-242236, 32711, -46208], ![56130, 76140, 0]]]
    h := ![![![297, -446, 1042], ![-22, -5508, 0]], ![![-541, 815, -1907], ![87, 10080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {49} * I37N2 =  Ideal.span {B.equivFun.symm ![17, 0, -2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E37RS2 


noncomputable def E41RS0 : RelationCertificate Table 49 ![![41, 0, 0], ![4, 1, 0]]
  ![4387, -623, 76] ![![49, 0, 0], ![-7, 0, 1]] where
    su := ![![2009, 0, 0], ![196, 49, 0]]
    hsu := by decide
    w := ![![214963, -30527, 3724], ![-124705, 11564, 2548]]
    hw := by decide
    g := ![![![398978115, -41751908, 3772163], ![-56919852, -127868364, 0]], ![![48531766, -5078184, 459001], ![-6923742, -15552888, 0]]]
    h := ![![![13110143, 19880156, 46487456], ![1763961, -272283660, 0]], ![![-7593467, -11514692, -26925769], ![-1021641, 157708083, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {49} * I41N0 =  Ideal.span {B.equivFun.symm ![4387, -623, 76]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 49 ![![41, 0, 0], ![14, 1, 0]]
  ![11231, 627, 595] ![![49, 0, 0], ![-19, 1, 0]] where
    su := ![![2009, 0, 0], ![686, 49, 0]]
    hsu := by decide
    w := ![![550319, 30723, 29155], ![-119315, -6664, -6321]]
    hw := by decide
    g := ![![![-84851308516, 1058761722254, -370955951935], ![54508909919, 2596691664800, 486]], ![![-30029689200, 374705894637, -131284857508], ![19291224316, 918994003000, 172]]]
    h := ![![![8435, 62813, 33887], ![4442, -198396, 0]], ![![-1837, -13619, -7347], ![-939, 43014, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {49} * I41N1 =  Ideal.span {B.equivFun.symm ![11231, 627, 595]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 7 ![![41, 0, 0], ![-18, 1, 0]]
  ![297, 5, -31] ![![7, 0, 0], ![3, -3, 1]] where
    su := ![![287, 0, 0], ![-126, 7, 0]]
    hsu := by decide
    w := ![![2079, 35, -217], ![14847, -2394, 476]]
    hw := by decide
    g := ![![![41705, 8753, 503], ![14200, 0, 0]], ![![-9793, -2052, -119], ![-3327, 0, 0]]]
    h := ![![![5191, -65238, 24069], ![-3857, -140980, 0]], ![![37305, -469220, 173119], ![-27809, -1013973, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {7} * I41N2 =  Ideal.span {B.equivFun.symm ![297, 5, -31]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E41RS2 


noncomputable def E43RS1 : RelationCertificate Table 7 ![![43, 0, 0], ![-14, 1, 0]]
  ![2115, 118, 112] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![301, 0, 0], ![-98, 7, 0]]
    hsu := by decide
    w := ![![14805, 826, 784], ![21938, 1225, 1162]]
    hw := by decide
    g := ![![![43543, -4395, 900], ![11819, 0, -2104]], ![![43500, -4390, 902], ![11805, 0, -2104]]]
    h := ![![![-73805, 648583, -303093], ![39144, 1861873, 0]], ![![-109366, 961053, -449115], ![57991, 2758873, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {7} * I43N1 =  Ideal.span {B.equivFun.symm ![2115, 118, 112]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 7 ![![47, 0, 0], ![-19, 1, 0]]
  ![155, -42, 18] ![![7, 0, 0], ![7, 0, 1]] where
    su := ![![329, 0, 0], ![-133, 7, 0]]
    hsu := by decide
    w := ![![1085, -294, 126], ![-4711, 462, 77]]
    hw := by decide
    g := ![![![1735770, -43812, -221206], ![1704175, -154167, 0]], ![![-621494, 15725, 79227], ![-610167, 55224, 0]]]
    h := ![![![3088, -38991, 13662], ![-2025, -91728, 0]], ![![-13268, 168597, -59075], ![8967, 396648, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {7} * I47N1 =  Ideal.span {B.equivFun.symm ![155, -42, 18]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E47RS1 


noncomputable def E61RS0 : RelationCertificate Table 7 ![![61, 0, 0], ![12, 1, 0]]
  ![45779, 2555, 2425] ![![7, 0, 0], ![7, 0, 1]] where
    su := ![![427, 0, 0], ![84, 7, 0]]
    hsu := by decide
    w := ![![320453, 17885, 16975], ![820883, 45815, 43484]]
    hw := by decide
    g := ![![![80, -5, -22], ![79, 0, 0]], ![![10, 3, -5], ![16, -1, 0]]]
    h := ![![![31605211, 183657941, 116969519], ![9228236, -1019305462, 0]], ![![80960965, 470464253, 299632986], ![23639294, -2611086562, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {7} * I61N0 =  Ideal.span {B.equivFun.symm ![45779, 2555, 2425]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 7 ![![61, 0, 0], ![19, 1, 0]]
  ![-5, 0, 1] ![![7, 0, 0], ![7, 0, 1]] where
    su := ![![427, 0, 0], ![133, 7, 0]]
    hsu := by decide
    w := ![![-35, 0, 7], ![7, 21, -7]]
    hw := by decide
    g := ![![![-8596094, 218405, 1096435], ![-8439459, 764416, 0]], ![![-2787020, 70811, 355484], ![-2736225, 247838, 0]]]
    h := ![![![-75, -730, -284], ![-20, 2475, 0]], ![![8, 136, 53], ![23, -462, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {7} * I61N1 =  Ideal.span {B.equivFun.symm ![-5, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 7 ![![61, 0, 0], ![30, 1, 0]]
  ![20067, 1120, 1063] ![![7, 0, 0], ![7, 0, 1]] where
    su := ![![427, 0, 0], ![210, 7, 0]]
    hsu := by decide
    w := ![![140469, 7840, 7441], ![359835, 20083, 19061]]
    hw := by decide
    g := ![![![4413, -115, -554], ![4334, -396, 0]], ![![2216, -60, -279], ![2180, -198, 0]]]
    h := ![![![11114965, 226468711, 54701196], ![9179020, -476681699, 0]], ![![28472881, 580137757, 140126329], ![23513554, -1221100478, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {7} * I61N2 =  Ideal.span {B.equivFun.symm ![20067, 1120, 1063]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E61RS2 


noncomputable def E67RS1 : RelationCertificate Table 7 ![![67, 0, 0], ![32, 1, 0]]
  ![15, 1, 1] ![![7, 0, 0], ![3, -3, 1]] where
    su := ![![469, 0, 0], ![224, 7, 0]]
    hsu := by decide
    w := ![![105, 7, 7], ![-231, 0, -14]]
    hw := by decide
    g := ![![![-10, 2, 0], ![3, 0, 0]], ![![-4, 1, 0], ![2, 0, 0]]]
    h := ![![![-291, -6095, -1377], ![-214, 13180, 0]], ![![597, 13428, 3034], ![564, -29040, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {7} * I67N1 =  Ideal.span {B.equivFun.symm ![15, 1, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 49 ![![71, 0, 0], ![-18, 1, 0]]
  ![39, -7, 2] ![![49, 0, 0], ![-11, 4, 1]] where
    su := ![![3479, 0, 0], ![-882, 49, 0]]
    hsu := by decide
    w := ![![1911, -343, 98], ![-245, 294, -196]]
    hw := by decide
    g := ![![![-3958, 536, -759], ![951, 1251, 0]], ![![978, -134, 185], ![-196, -306, 0]]]
    h := ![![![232213, -2428795, 895302], ![-93042, -9080920, 0]], ![![-30219, 316114, -116526], ![12126, 1181906, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {49} * I71N1 =  Ideal.span {B.equivFun.symm ![39, -7, 2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 49 ![![73, 0, 0], ![-29, 1, 0]]
  ![-29, 1, 0] ![![49, 0, 0], ![-18, 4, 1]] where
    su := ![![3577, 0, 0], ![-1421, 49, 0]]
    hsu := by decide
    w := ![![-1421, 49, 0], ![686, -147, 0]]
    hw := by decide
    g := ![![![-5349, -28, 169], ![2022, 0, 448]], ![![2107, 7, -67], ![-742, 0, -175]]]
    h := ![![![11255, -212659, 49644], ![-7372, -517716, 0]], ![![-5614, 106329, -24822], ![3720, 258858, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {49} * I73N1 =  Ideal.span {B.equivFun.symm ![-29, 1, 0]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 7 ![![79, 0, 0], ![11, 1, 0]]
  ![-265, -15, -14] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![553, 0, 0], ![77, 7, 0]]
    hsu := by decide
    w := ![![-1855, -105, -98], ![-2744, -154, -147]]
    hw := by decide
    g := ![![![-14193, 1433, -295], ![-3845, 0, 686]], ![![-2031, 204, -42], ![-544, 0, 98]]]
    h := ![![![126373, 649543, 454909], ![25838, -5133975, 0]], ![![186936, 960846, 672931], ![38244, -7594510, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {7} * I79N1 =  Ideal.span {B.equivFun.symm ![-265, -15, -14]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS1 
