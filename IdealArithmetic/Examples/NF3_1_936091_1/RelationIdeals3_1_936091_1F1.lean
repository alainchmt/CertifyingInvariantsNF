import IdealArithmetic.Examples.NF3_1_936091_1.PrimesBelow3_1_936091_1F1
import IdealArithmetic.Examples.NF3_1_936091_1.ClassGroupData3_1_936091_1

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 36 ![![41, 0, 0], ![8, 1, 0]]
  ![-47, -3, 1] ![![36, 0, 0], ![2, 1, 0]] where
    su := ![![1476, 0, 0], ![288, 36, 0]]
    hsu := by decide
    w := ![![-1692, -108, 36], ![-288, -36, 0]]
    hw := by decide
    g := ![![![-1, -279, -139], ![25, 5005, 0]], ![![0, -78, -39], ![-1, 1404, 0]]]
    h := ![![![-9055, -1196, -8], ![46401, 329, 0]], ![![-1544, -209, -2], ![7912, 82, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {36} * I41N0 =  Ideal.span {B.equivFun.symm ![-47, -3, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 3 ![![41, 0, 0], ![-7, 1, 0]]
  ![-151, -30, -1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![123, 0, 0], ![-21, 3, 0]]
    hsu := by decide
    w := ![![-453, -90, -3], ![345, -138, -30]]
    hw := by decide
    g := ![![![-2790, -4794, 5558], ![-667, -16928, 0]], ![![823, 670, -831], ![-48, 2576, 0]]]
    h := ![![![-199, 34, -1], ![-1144, 40, 0]], ![![165, -19, -1], ![950, 31, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {3} * I41N1 =  Ideal.span {B.equivFun.symm ![-151, -30, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 2 ![![41, 0, 0], ![-2, 1, 0]]
  ![9613, -2345, 317] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![82, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![19226, -4690, 634], ![-61498, 15002, -2028]]
    hw := by decide
    g := ![![![169, 54, 68], ![28, -123, 0]], ![![-39, 2, -3], ![3, 9, 0]]]
    h := ![![![30705, -15325, 24], ![624646, -667, 0]], ![![-98209, 49023, -80], ![-1997910, 2266, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {2} * I41N2 =  Ideal.span {B.equivFun.symm ![9613, -2345, 317]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E41RS2 


noncomputable def E43RS1 : RelationCertificate Table 9 ![![43, 0, 0], ![5, 1, 0]]
  ![-785, 114, 37] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![387, 0, 0], ![45, 9, 0]]
    hsu := by decide
    w := ![![-7065, 1026, 333], ![-8748, 72, 225]]
    hw := by decide
    g := ![![![-8255, 2250, -296], ![-1577, 110, 0]], ![![267, -79, 7], ![57, 20, 0]]]
    h := ![![![-29085, -5905, -18], ![249974, 811, 0]], ![![-36044, -7317, -22], ![309784, 971, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {9} * I43N1 =  Ideal.span {B.equivFun.symm ![-785, 114, 37]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 12 ![![53, 0, 0], ![-9, 1, 0]]
  ![-3526301, 860211, -116285] ![![12, 0, 0], ![2, 1, 0]] where
    su := ![![636, 0, 0], ![-108, 12, 0]]
    hsu := by decide
    w := ![![-42315612, 10322532, -1395420], ![15506688, -3782724, 511356]]
    hw := by decide
    g := ![![![6991, -489662, -246577], ![-39633, 2959276, 0]], ![![-1243, 79523, 40042], ![6421, -480501, 0]]]
    h := ![![![-4712371, 543162, -3386], ![-27358818, 63173, 0]], ![![1726880, -199038, 1240], ![10025824, -23107, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {12} * I53N1 =  Ideal.span {B.equivFun.symm ![-3526301, 860211, -116285]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E53RS1 


noncomputable def E59RS0 : RelationCertificate Table 4 ![![59, 0, 0], ![28, 1, 0]]
  ![-275, -11, 5] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![236, 0, 0], ![112, 4, 0]]
    hsu := by decide
    w := ![![-1100, -44, 20], ![-1520, -212, 4]]
    hw := by decide
    g := ![![![1611, -712, 21], ![629, 170, 0]], ![![590, -270, 3], ![230, 81, 0]]]
    h := ![![![-1893, -98, -1], ![3979, 64, 0]], ![![-2628, -123, -1], ![5524, 60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {4} * I59N0 =  Ideal.span {B.equivFun.symm ![-275, -11, 5]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 6 ![![59, 0, 0], ![-28, 1, 0]]
  ![-10547, 1275, 457] ![![6, 0, 0], ![2, 1, 0]] where
    su := ![![354, 0, 0], ![-168, 6, 0]]
    hsu := by decide
    w := ![![-63282, 7650, 2742], ![-109752, -228, 2646]]
    hw := by decide
    g := ![![![4424681, -35761418, -17800559], ![-4485340, 107382995, 0]], ![![-2419890, 17654500, 8740589], ![2135791, -52781469, 0]]]
    h := ![![![-145261, 5840, -15], ![-305709, 1342, 0]], ![![-251732, 10084, -32], ![-529782, 2329, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {6} * I59N1 =  Ideal.span {B.equivFun.symm ![-10547, 1275, 457]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 9 ![![59, 0, 0], ![-1, 1, 0]]
  ![-619, 12, 17] ![![9, 0, 0], ![2, 1, 0]] where
    su := ![![531, 0, 0], ![-9, 9, 0]]
    hsu := by decide
    w := ![![-5571, 108, 153], ![-4536, -306, 63]]
    hw := by decide
    g := ![![![-2135, 383, -178], ![-430, 940, 0]], ![![267, -79, 7], ![57, 20, 0]]]
    h := ![![![-20, 10, 0], ![-561, 17, 0]], ![![-16, 7, 0], ![-440, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {9} * I59N2 =  Ideal.span {B.equivFun.symm ![-619, 12, 17]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E59RS2 


noncomputable def E67RS0 : RelationCertificate Table 36 ![![67, 0, 0], ![12, 1, 0]]
  ![562795, -137289, 18559] ![![36, 0, 0], ![2, 1, 0]] where
    su := ![![2412, 0, 0], ![432, 36, 0]]
    hsu := by decide
    w := ![![20260620, -4942404, 668124], ![-2474856, 603720, -81612]]
    hw := by decide
    g := ![![![213, 1581, 791], ![88, -28743, 0]], ![![58, 283, 141], ![45, -5135, 0]]]
    h := ![![![2417401, 206069, 891], ![-13450256, -41138, 0]], ![![-295294, -25174, -109], ![1642996, 5036, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {36} * I67N0 =  Ideal.span {B.equivFun.symm ![562795, -137289, 18559]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 3 ![![67, 0, 0], ![16, 1, 0]]
  ![-6853915, 1671954, -226018] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![201, 0, 0], ![48, 3, 0]]
    hsu := by decide
    w := ![![-20561745, 5015862, -678054], ![50701407, -12368175, 1671954]]
    hw := by decide
    g := ![![![10006, 6895, -5726], ![-1035, 16856, 0]], ![![2690, 1847, -1418], ![-278, 4214, 0]]]
    h := ![![![-29539961, -1932125, -10700], ![123270217, 490882, 0]], ![![72839959, 4764204, 26381], ![-303961049, -1210209, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3} * I67N1 =  Ideal.span {B.equivFun.symm ![-6853915, 1671954, -226018]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 2 ![![67, 0, 0], ![-29, 1, 0]]
  ![151, -37, 5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![134, 0, 0], ![-58, 2, 0]]
    hsu := by decide
    w := ![![302, -74, 10], ![-970, 236, -32]]
    hw := by decide
    g := ![![![-76, -5, 5074], ![-1, -10146, 0]], ![![30, 1, -2003], ![1, 4005, 0]]]
    h := ![![![9039, -339, 1], ![20878, -62, 0]], ![![-28983, 1139, -5], ![-66944, 319, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {2} * I67N2 =  Ideal.span {B.equivFun.symm ![151, -37, 5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E67RS2 


noncomputable def E71RS1 : RelationCertificate Table 6 ![![71, 0, 0], ![-18, 1, 0]]
  ![-23, 3, 1] ![![6, 0, 0], ![2, 1, 0]] where
    su := ![![426, 0, 0], ![-108, 6, 0]]
    hsu := by decide
    w := ![![-138, 18, 6], ![-240, 0, 6]]
    hw := by decide
    g := ![![![107, -2421, -1243], ![-364, 7455, 0]], ![![-28, 624, 321], ![99, -1925, 0]]]
    h := ![![![-13, 1, 0], ![-50, 1, 0]], ![![-32, 2, 0], ![-124, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {6} * I71N1 =  Ideal.span {B.equivFun.symm ![-23, 3, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E71RS1 
