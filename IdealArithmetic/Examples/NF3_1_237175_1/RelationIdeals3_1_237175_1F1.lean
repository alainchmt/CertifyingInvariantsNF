import IdealArithmetic.Examples.NF3_1_237175_1.PrimesBelow3_1_237175_1F1
import IdealArithmetic.Examples.NF3_1_237175_1.ClassGroupData3_1_237175_1

set_option linter.all false

noncomputable section


noncomputable def E47RS0 : RelationCertificate Table 4 ![![47, 0, 0], ![19, 1, 0]]
  ![15982, -556, 657] ![![4, 0, 0], ![34, 0, 2]] where
    su := ![![188, 0, 0], ![76, 4, 0]]
    hsu := by decide
    w := ![![63928, -2224, 2628], ![531668, -18496, 21856]]
    hw := by decide
    g := ![![![-8, 8, 16], ![3, 0, 0]], ![![-6, -30, 22], ![-13, -7, 0]]]
    h := ![![![16576, 184662, 41103], ![10658, -482796, 0]], ![![137923, 1535776, 341840], ![88476, -4015254, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {4} * I47N0 =  Ideal.span {B.equivFun.symm ![15982, -556, 657]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 4 ![![47, 0, 0], ![-12, 1, 0]]
  ![-1056658, -816960, 204195] ![![4, 0, 0], ![34, 0, 2]] where
    su := ![![188, 0, 0], ![-48, 4, 0]]
    hsu := by decide
    w := ![![-4226632, -3267840, 816780], ![1657028, 3269640, -7831496]]
    hw := by decide
    g := ![![![301226926968, -716296854045, -347032400204], ![2386912679263, 0, 0]], ![![-85785904273, 203992962891, 98830767097], ![-679764802710, -7, 0]]]
    h := ![![![-290639298, 2083177258, -641754587], ![118528712, 7540667446, 0]], ![![110705697, -793477832, 244406286], ![-45147763, -2872263329, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {4} * I47N1 =  Ideal.span {B.equivFun.symm ![-1056658, -816960, 204195]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E47RS1 


noncomputable def E53RS0 : RelationCertificate Table 4 ![![53, 0, 0], ![11, 1, 0]]
  ![-10, -8, 3] ![![4, 0, 0], ![34, 0, 2]] where
    su := ![![212, 0, 0], ![44, 4, 0]]
    hsu := by decide
    w := ![![-40, -32, 12], ![-44, -8, -88]]
    hw := by decide
    g := ![![![-40, 91, 44], ![-303, 0, 0]], ![![-17, -8, 21], ![-67, -7, 0]]]
    h := ![![![199, 1115, 447], ![117, -5922, 0]], ![![229, 1254, 502], ![106, -6657, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {4} * I53N0 =  Ideal.span {B.equivFun.symm ![-10, -8, 3]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS0 


noncomputable def E59RS0 : RelationCertificate Table 2 ![![59, 0, 0], ![8, 1, 0]]
  ![-8003799, -4763311, -3835516] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![118, 0, 0], ![16, 2, 0]]
    hsu := by decide
    w := ![![-16007598, -9526622, -7671032], ![113209890, 88811896, -26724276]]
    hw := by decide
    g := ![![![-5691465025704948, 158398504985010, -233967742968086], ![79199252492507, 0, 0]], ![![-638114511325395, 17759291174887, -26231947538234], ![8879645587445, 0, 0]]]
    h := ![![![-211793573, -759919701, -434661588], ![-41597760, 6410299544, 0]], ![![1490072599, 5346579708, 3057366362], ![292663794, -45099494374, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {2} * I59N0 =  Ideal.span {B.equivFun.symm ![-8003799, -4763311, -3835516]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 2 ![![59, 0, 0], ![10, 1, 0]]
  ![209865584, -7300931, 8627265] ![![2, 0, 0], ![17, -1, 1]] where
    su := ![![118, 0, 0], ![20, 2, 0]]
    hsu := by decide
    w := ![![419731168, -14601862, 17254530], ![3781437522, -131550938, 155449326]]
    hw := by decide
    g := ![![![339, 2288, -3320], ![179, 0, 0]], ![![153, 1798, -625], ![234, 0, 0]]]
    h := ![![![-820424304, -3860539177, -1717134365], ![-204487788, 25329888700, 0]], ![![-7391357751, -34780328004, -15469988443], ![-1842269533, 228201760700, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {2} * I59N1 =  Ideal.span {B.equivFun.symm ![209865584, -7300931, 8627265]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 4 ![![59, 0, 0], ![-19, 1, 0]]
  ![-466266, -356688, 75721] ![![4, 0, 0], ![34, 0, 2]] where
    su := ![![236, 0, 0], ![-76, 4, 0]]
    hsu := by decide
    w := ![![-1865064, -1426752, 302884], ![1523076, 1964792, -3267936]]
    hw := by decide
    g := ![![![-53452851035, 127107192617, 61581052447], ![-423558707495, 0, 0]], ![![18468458378, -43916720124, -21276827742], ![146343482365, -7, 0]]]
    h := ![![![-89248867, 1040993407, -208355845], ![46385179, 3073267644, 0]], ![![71618242, -835345791, 167183152], ![-37221893, -2466155738, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {4} * I59N2 =  Ideal.span {B.equivFun.symm ![-466266, -356688, 75721]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS2 


noncomputable def E61RS1 : RelationCertificate Table 4 ![![61, 0, 0], ![-10, 1, 0]]
  ![218014, 149520, 29785] ![![4, 0, 0], ![34, 0, 2]] where
    su := ![![244, 0, 0], ![-40, 4, 0]]
    hsu := by decide
    w := ![![872056, 598080, 119140], ![-4301324, -3284680, 676688]]
    hw := by decide
    g := ![![![10461435884, -24876572945, -12052233330], ![82896088465, 0, 0]], ![![-1952524136, 4642967706, 2249430804], ![-15471739622, 7, 0]]]
    h := ![![![-288070, 1672598, -607283], ![74674, 9268512, 0]], ![![1399845, -8130660, 2956644], ![-362718, -45046528, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {4} * I61N1 =  Ideal.span {B.equivFun.symm ![218014, 149520, 29785]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 4 ![![67, 0, 0], ![-9, 1, 0]]
  ![46, -20, 201] ![![4, 0, 0], ![34, 0, 2]] where
    su := ![![268, 0, 0], ![-36, 4, 0]]
    hsu := by decide
    w := ![![184, -80, 804], ![-11628, -7760, -2400]]
    hw := by decide
    g := ![![![84501, -200970, -97367], ![669693, 0, 0]], ![![-13107, 31126, 15105], ![-103815, -7, 0]]]
    h := ![![![18070, -92824, 37155], ![-3772, -622296, 0]], ![![-1117605, 5742688, -2298504], ![235884, 38499792, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {4} * I67N1 =  Ideal.span {B.equivFun.symm ![46, -20, 201]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E67RS1 


noncomputable def E71RS0 : RelationCertificate Table 2 ![![71, 0, 0], ![21, 1, 0]]
  ![-347, -223, -104] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![142, 0, 0], ![42, 2, 0]]
    hsu := by decide
    w := ![![-694, -446, -208], ![2882, 2372, -1100]]
    hw := by decide
    g := ![![![5984014, -166541, 245994], ![-83269, 0, 0]], ![![1653185, -46010, 67960], ![-23004, 0, 0]]]
    h := ![![![44057, 499801, 100016], ![20106, -1775310, 0]], ![![-182249, -2066906, -413626], ![-82968, 7341724, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {2} * I71N0 =  Ideal.span {B.equivFun.symm ![-347, -223, -104]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 2 ![![71, 0, 0], ![-19, 1, 0]]
  ![-6502684, -3269079, -5385871] ![![2, 0, 0], ![17, -1, 1]] where
    su := ![![142, 0, 0], ![-38, 2, 0]]
    hsu := by decide
    w := ![![-13005368, -6538158, -10771742], ![22146542, 4573674, 43122442]]
    hw := by decide
    g := ![![![-146944587785759, -212574283317130, 154405557611698], ![-1065539075714407, 0, 0]], ![![42189757460018, 61032921256448, -44331901734387], ![305930526914799, 0, 0]]]
    h := ![![![-1232496521, 13716239844, -2744806301], ![523009497, 48718965375, 0]], ![![2109991046, -23481781038, 4699188511], ![-895374765, -83405205765, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {2} * I71N1 =  Ideal.span {B.equivFun.symm ![-6502684, -3269079, -5385871]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 4 ![![71, 0, 0], ![-3, 1, 0]]
  ![462, -16, 19] ![![4, 0, 0], ![34, 0, 2]] where
    su := ![![284, 0, 0], ![-12, 4, 0]]
    hsu := by decide
    w := ![![1848, -64, 76], ![15364, -536, 632]]
    hw := by decide
    g := ![![![-4, -9, 0], ![-1, 0, 0]], ![![-18, -24, 12], ![-11, -7, 0]]]
    h := ![![![12825, -25697, 25709], ![-849, -456330, 0]], ![![106607, -213636, 213742], ![-7502, -3793881, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {4} * I71N2 =  Ideal.span {B.equivFun.symm ![462, -16, 19]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E71RS2 


noncomputable def E79RS0 : RelationCertificate Table 2 ![![79, 0, 0], ![4, 1, 0]]
  ![127403641, -4432195, 5237376] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![254807282, -8864390, 10474752], ![-176460422, 6138812, -7254028]]
    hw := by decide
    g := ![![![-1942, -502, -2926], ![-251, 0, 0]], ![![1071, 672, -254], ![337, 0, 0]]]
    h := ![![![-8111935489, -12206153022, -16284269496], ![-565239127, 321615631890, 0]], ![![5617718407, 8453066553, 11277264310], ![391442347, -222726876876, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {2} * I79N0 =  Ideal.span {B.equivFun.symm ![127403641, -4432195, 5237376]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![12, 1, 0]]
  ![-395733, 13767, -16268] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![24, 2, 0]]
    hsu := by decide
    w := ![![-791466, 27534, -32536], ![548110, -19068, 22532]]
    hw := by decide
    g := ![![![-458, -284, 90], ![-141, 0, 0]], ![![-115, -66, -2], ![-33, 0, 0]]]
    h := ![![![7356873, 41845878, 15223996], ![1647273, -300677988, 0]], ![![-5094829, -28979318, -10542998], ![-1140709, 208227027, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![-395733, 13767, -16268]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E79RS1 
