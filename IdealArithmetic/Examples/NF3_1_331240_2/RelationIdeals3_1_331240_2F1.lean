import IdealArithmetic.Examples.NF3_1_331240_2.PrimesBelow3_1_331240_2F1
import IdealArithmetic.Examples.NF3_1_331240_2.ClassGroupData3_1_331240_2

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 6 ![![43, 0, 0], ![-16, 1, 0]]
  ![-3410378, -201050, -370889] ![![6, 0, 0], ![-2, 1, 0]] where
    su := ![![258, 0, 0], ![-96, 6, 0]]
    hsu := by decide
    w := ![![-20462268, -1206300, -2225334], ![-33977034, -2003028, -3695106]]
    hw := by decide
    g := ![![![12547, 220296, -354553], ![32539, 193250, 0]], ![![190471262968, 3809425282761, -6135895723418], ![571413792808, 3346852212843, 0]]]
    h := ![![![-368751870, 26664137, -1908366], ![-990807502, 7426259, 0]], ![![-612302373, 44275043, -3168776], ![-1645208700, 12331047, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {6} * I43N1 =  Ideal.span {B.equivFun.symm ![-3410378, -201050, -370889]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E43RS1 


noncomputable def E53RS0 : RelationCertificate Table 18 ![![53, 0, 0], ![11, 1, 0]]
  ![-68, 4, 1] ![![18, 0, 0], ![4, 1, 0]] where
    su := ![![954, 0, 0], ![198, 18, 0]]
    hsu := by decide
    w := ![![-1224, 72, 18], ![-162, -72, 54]]
    hw := by decide
    g := ![![![-9, -185, 2028], ![1, -3320, 0]], ![![469, -40188, 443365], ![-2127, -725507, 0]]]
    h := ![![![1, -2013, -3691], ![-11, 17784, 0]], ![![-1, -262, -480], ![4, 2313, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {18} * I53N0 =  Ideal.span {B.equivFun.symm ![-68, 4, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 18 ![![53, 0, 0], ![20, 1, 0]]
  ![-6356, -488, 661] ![![18, 0, 0], ![4, 1, 0]] where
    su := ![![954, 0, 0], ![360, 18, 0]]
    hsu := by decide
    w := ![![-114408, -8784, 11898], ![47286, -5868, 1242]]
    hw := by decide
    g := ![![![91193, -228567, 2579933], ![7583, -4205180, 0]], ![![17225306, -1459614308, 16103015360], ![-77261822, -26350378803, 0]]]
    h := ![![![148908, 7372, -39], ![-394924, 248, 0]], ![![-63321, -3156, 15], ![167932, -66, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {18} * I53N1 =  Ideal.span {B.equivFun.symm ![-6356, -488, 661]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 18 ![![53, 0, 0], ![21, 1, 0]]
  ![2104, 124, 229] ![![18, 0, 0], ![4, 1, 0]] where
    su := ![![954, 0, 0], ![378, 18, 0]]
    hsu := by decide
    w := ![![37872, 2232, 4122], ![33606, 1980, 3654]]
    hw := by decide
    g := ![![![-17, -12, 153], ![13, -252, 0]], ![![2505, -213717, 2357803], ![-11307, -3858223, 0]]]
    h := ![![![-1945, 304415, 209353], ![5009, -1008680, 0]], ![![-1726, 270125, 185771], ![4445, -895060, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {18} * I53N2 =  Ideal.span {B.equivFun.symm ![2104, 124, 229]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E53RS2 


noncomputable def E59RS0 : RelationCertificate Table 2 ![![59, 0, 0], ![13, 1, 0]]
  ![221, 13, 24] ![![2, 0, 0], ![-2, -1, 1]] where
    su := ![![118, 0, 0], ![26, 2, 0]]
    hsu := by decide
    w := ![![442, 26, 48], ![988, 58, 108]]
    hw := by decide
    g := ![![![67, -23, 17], ![-47, 0, 0]], ![![7, -1, 1], ![-6, 0, 0]]]
    h := ![![![4264, 332, 6], ![-19335, -30, 0]], ![![9568, 749, 19], ![-43386, -97, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {2} * I59N0 =  Ideal.span {B.equivFun.symm ![221, 13, 24]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 2 ![![59, 0, 0], ![22, 1, 0]]
  ![-197, -19, 23] ![![2, 0, 0], ![-2, -1, 1]] where
    su := ![![118, 0, 0], ![44, 2, 0]]
    hsu := by decide
    w := ![![-394, -38, 46], ![-1696, 370, -148]]
    hw := by decide
    g := ![![![10363, -2311, 5160], ![-6625, 0, 0]], ![![5966, -1330, 2970], ![-3813, 0, 0]]]
    h := ![![![-7895, -389, -19], ![21164, 104, 0]], ![![-33828, -1654, -79], ![90682, 417, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {2} * I59N1 =  Ideal.span {B.equivFun.symm ![-197, -19, 23]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 2 ![![59, 0, 0], ![23, 1, 0]]
  ![-7, -1, 1] ![![2, 0, 0], ![-2, -1, 1]] where
    su := ![![118, 0, 0], ![46, 2, 0]]
    hsu := by decide
    w := ![![-14, -2, 2], ![-96, 14, -4]]
    hw := by decide
    g := ![![![-19, 5, -10], ![13, 0, 0]], ![![-11, 3, -6], ![8, 0, 0]]]
    h := ![![![-43, -15, -8], ![110, 43, 0]], ![![-308, -23, -6], ![788, 32, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {2} * I59N2 =  Ideal.span {B.equivFun.symm ![-7, -1, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E59RS2 


noncomputable def E61RS1 : RelationCertificate Table 9 ![![61, 0, 0], ![-10, 1, 0]]
  ![889, 322, -257] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![549, 0, 0], ![-90, 9, 0]]
    hsu := by decide
    w := ![![8001, 2898, -2313], ![-24714, 567, 972]]
    hw := by decide
    g := ![![![-43445, -965, -5091], ![-19411, -468, 0]], ![![-1400, -22, -269], ![-620, 71, 0]]]
    h := ![![![82679, -8691, 311], ![504253, -1748, 0]], ![![-256066, 26961, -994], ![-1561728, 5522, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {9} * I61N1 =  Ideal.span {B.equivFun.symm ![889, 322, -257]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 3 ![![67, 0, 0], ![10, 1, 0]]
  ![503, -22, -13] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![201, 0, 0], ![30, 3, 0]]
    hsu := by decide
    w := ![![1509, -66, -39], ![-927, 591, -333]]
    hw := by decide
    g := ![![![-26847, 130458, -394573], ![34538, 107156, 0]], ![![-6586, 20619, -62352], ![4678, 16856, 0]]]
    h := ![![![13379, 1341, 9], ![-89589, -56, 0]], ![![-8237, -825, -12], ![55157, 63, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3} * I67N1 =  Ideal.span {B.equivFun.symm ![503, -22, -13]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 6 ![![71, 0, 0], ![-26, 1, 0]]
  ![2528582, 149066, 274991] ![![6, 0, 0], ![-2, 1, 0]] where
    su := ![![426, 0, 0], ![-156, 6, 0]]
    hsu := by decide
    w := ![![15171492, 894396, 1649946], ![25191846, 1485120, 2739690]]
    hw := by decide
    g := ![![![-1525, -188, 564], ![481, -374, 0]], ![![-171016982, -3420347390, 5509202258], ![-513052232, -3005019367, 0]]]
    h := ![![![489958214, -21054649, 789334], ![1337865562, -5069793, 0]], ![![813562207, -34960653, 1310662], ![2221489156, -8418217, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {6} * I71N1 =  Ideal.span {B.equivFun.symm ![2528582, 149066, 274991]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 18 ![![73, 0, 0], ![-36, 1, 0]]
  ![514, -26, -11] ![![18, 0, 0], ![4, 1, 0]] where
    su := ![![1314, 0, 0], ![-648, 18, 0]]
    hsu := by decide
    w := ![![9252, -468, -198], ![846, 540, -396]]
    hw := by decide
    g := ![![![438, 73, -517], ![103, 928, 0]], ![![-866, 61160, -674839], ![3214, 1104255, 0]]]
    h := ![![![340930, -11644, 583], ![691316, -3870, 0]], ![![30935, -1024, 44], ![62728, -294, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {18} * I73N1 =  Ideal.span {B.equivFun.symm ![514, -26, -11]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 6 ![![79, 0, 0], ![-28, 1, 0]]
  ![-4699, -277, -511] ![![6, 0, 0], ![-2, -1, 1]] where
    su := ![![474, 0, 0], ![-168, 6, 0]]
    hsu := by decide
    w := ![![-28194, -1662, -3066], ![-21072, -1242, -2292]]
    hw := by decide
    g := ![![![-3833, 104, -18], ![1264, 221, 0]], ![![1366, -39, 7], ![-443, -78, 0]]]
    h := ![![![-2941, -728701, 242927], ![-8130, -1744704, 0]], ![![-2204, -544626, 181562], ![-6093, -1303980, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {6} * I79N1 =  Ideal.span {B.equivFun.symm ![-4699, -277, -511]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E79RS1 
