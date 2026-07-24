import IdealArithmetic.Examples.NF5_1_48600000_1.PrimesBelow5_1_48600000_1F0
import IdealArithmetic.Examples.NF5_1_48600000_1.ClassGroupData5_1_48600000_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0, 0, 0], ![1, 2, 1, 0, 0]]
  ![-21, -3, -8, 7, 10] ![![2, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] where
    su := ![![4, 0, 0, 0, 0], ![2, 4, 2, 0, 0]]
    hsu := by decide
    w := ![![-42, -6, -16, 14, 20], ![4, 22, -16, -12, -44]]
    hw := by decide
    g := ![![![26, -23, -8, -5, 2], ![13, 7, 0, 0, 0]], ![![1547, -5034, -1172, -1949, -8], ![-1553, 3892, -3, 0, 0]]]
    h := ![![![170, -166, -145, -67, 112], ![-149, 189, 14, 0, 30]], ![![-389, 373, 326, 180, -218], ![342, -429, -45, 0, -66]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![-21, -3, -8, 7, 10]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
  ![1, 0, 0, 0, 0] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]] where
    su := ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
    hsu := by decide
    w := ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]]
    hw := by decide
    g := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-4, -5, 2, 2, 4], ![1, 2, 0, 0, 0]]]
    h := ![![![1, 0, 0, 0, 0], ![0, 0, 0, 0, 0]], ![![-4, -5, 2, 2, 4], ![1, 2, 0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 4 ![![2, 0, 0, 0, 0], ![1, -3, 1, 1, 2]]
  ![-2, 3, -3, -1, -5] ![![4, 0, 0, 0, 0], ![10, -7, 5, 2, 6]] where
    su := ![![8, 0, 0, 0, 0], ![4, -12, 4, 4, 8]]
    hsu := by decide
    w := ![![-8, 12, -12, -4, -20], ![-20, -32, 16, 24, 76]]
    hw := by decide
    g := ![![![-1773, 462, -136, 350, 604], ![346, -155, 0, 0, 179]], ![![-1990, -234, -336, 177, 178], ![133, 217, 0, 0, -7]]]
    h := ![![![28779, 4410, 972, -4019, -2924], ![3328, -4991, 212, 0, 35]], ![![-16832, -2575, -569, 2350, 1713], ![-1941, 2919, -124, 0, -21]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {4} * I2N2 =  Ideal.span {B.equivFun.symm ![-2, 3, -3, -1, -5]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E2RS2 


noncomputable def E3RS0 : RelationCertificate Table 4 ![![3, 0, 0, 0, 0], ![0, 1, 0, 0, 0]]
  ![131, -5, 70, -31, -14] ![![4, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] where
    su := ![![12, 0, 0, 0, 0], ![0, 4, 0, 0, 0]]
    hsu := by decide
    w := ![![524, -20, 280, -124, -56], ![-236, -84, -48, 104, 212]]
    hw := by decide
    g := ![![![21885, -169724, -49253, -60202, 38], ![-43798, 240875, -45, 0, 0]], ![![7291, -56577, -16424, -20068, 9], ![-14601, 80276, -15, 0, 0]]]
    h := ![![![1965, -28662, -60795, 0, 3838], ![-9554, 95535, 5733, -1441, 0]], ![![-885, 12797, 27160, 0, -1713], ![4268, -42680, -2570, 649, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4} * I3N0 =  Ideal.span {B.equivFun.symm ![131, -5, 70, -31, -14]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 2 ![![3, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![431, 290, 375, 160, 189] ![![2, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] where
    su := ![![6, 0, 0, 0, 0], ![2, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![862, 580, 750, 320, 378], ![3504, 2450, 2894, 1200, 1384]]
    hw := by decide
    g := ![![![-314701, 1022466, 235827, 393286, -17], ![314448, -786399, -55, 0, 0]], ![![-125931, 408893, 94406, 157404, 255], ![125723, -314559, -22, 0, 0]]]
    h := ![![![158, -131, 261, 0, 567], ![713, -15, 1105, -189, 0]], ![![668, -395, 979, 0, 2076], ![2516, -53, 4060, -692, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {2} * I3N1 =  Ideal.span {B.equivFun.symm ![431, 290, 375, 160, 189]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 2 ![![3, 0, 0, 0, 0], ![-1, 1, 0, 0, 0]]
  ![102, 17, 37, -35, -53] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]] where
    su := ![![6, 0, 0, 0, 0], ![-2, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![204, 34, 74, -70, -106], ![-226, -70, -54, 94, 182]]
    hw := by decide
    g := ![![![389535187, 704476849, -286334199, -263500502, -549892748], ![46015247, -263384550, 115962, 22, 0]], ![![13, 68, 63, 33, 31], ![21, 3, 0, 0, 0]]]
    h := ![![![518, -229, 337, 0, 481], ![704, 226, 526, -187, 0]], ![![-532, 228, -339, 0, -479], ![-719, -222, -526, 191, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {2} * I3N2 =  Ideal.span {B.equivFun.symm ![102, 17, 37, -35, -53]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS2 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0, 0, 0], ![1, 1, 0, 0, 0]]
  ![19, 2, 3, 0, 1] ![![2, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] where
    su := ![![22, 0, 0, 0, 0], ![2, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![38, 4, 6, 0, 2], ![32, 26, 22, 8, 8]]
    hw := by decide
    g := ![![![-49647, 161365, 37285, 62107, 79], ![49680, -124141, -33, 0, 0]], ![![-8991, 29232, 6755, 11249, 11], ![9003, -22489, -6, 0, 0]]]
    h := ![![![198, 61, 71, 0, 275], ![-647, -11, 1890, -378, 0]], ![![170, 53, 61, 0, 236], ![-558, -6, 1624, -324, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![19, 2, 3, 0, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 2 ![![11, 0, 0, 0, 0], ![-5, 1, 0, 0, 0]]
  ![-371, 31, -212, 79, 6] ![![2, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] where
    su := ![![22, 0, 0, 0, 0], ![-10, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![-742, 62, -424, 158, 12], ![816, 202, 240, -314, -556]]
    hw := by decide
    g := ![![![-689223, 2241266, 517900, 862767, 1148], ![690363, -1724472, -516, 0, 0]], ![![229715, -747017, -172662, -287612, -428], ![-230123, 574827, 172, 0, 0]]]
    h := ![![![-2948, -42832, 10074, 2207, -3518], ![-2541, -118431, -19360, 4838, 0]], ![![3727, 53960, -11766, -2943, 4430], ![3217, 149169, 26090, -6126, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {2} * I11N2 =  Ideal.span {B.equivFun.symm ![-371, 31, -212, 79, 6]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS2 


noncomputable def E13RS1 : RelationCertificate Table 2 ![![13, 0, 0, 0, 0], ![4, -9, 1, 1, 2]]
  ![-6, 9, -11, -3, -17] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]] where
    su := ![![26, 0, 0, 0, 0], ![8, -18, 2, 2, 4]]
    hsu := by decide
    w := ![![-12, 18, -22, -6, -34], ![46, -26, 42, 2, 42]]
    hw := by decide
    g := ![![![2584584483, 4679354933, -1903511001, -1748691926, -3650188227], ![297548915, -1752723630, -4030938, -510, 0]], ![![775820210, 1404611893, -571380944, -524908570, -1095684751], ![89315890, -526118775, -1209975, -153, 0]]]
    h := ![![![24134, -2052, -24498, -2494, -919], ![6637, -28134, 336, 0, 0]], ![![-18409, 1574, 18684, 1900, 699], ![-5049, 21456, -258, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {2} * I13N1 =  Ideal.span {B.equivFun.symm ![-6, 9, -11, -3, -17]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 4 ![![19, 0, 0, 0, 0], ![6, 1, 0, 0, 0]]
  ![144, -203, -111, -59, -29] ![![4, 0, 0, 0, 0], ![10, -7, 5, 2, 6]] where
    su := ![![76, 0, 0, 0, 0], ![24, 4, 0, 0, 0]]
    hsu := by decide
    w := ![![576, -812, -444, -236, -116], ![-724, -3424, -676, -20, 584]]
    hw := by decide
    g := ![![![16162560529970, 11047510408869, -1176584742443, -4885924969879, -9672767072313], ![2650414087967, -2848572969366, 1142223, 133, 0]], ![![5954627557964, 4070135409880, -433478588954, -1800077618738, -3563651023255], ![976468347224, -1049474250867, 420819, 49, 0]]]
    h := ![![![4881696, 876809, 3997643, 851683, 46657], ![-15384804, -182110, -15073896, -110814, 0]], ![![22582267, 4056066, 18492153, 3939807, 215934], ![-71168659, -842493, -69728088, -512825, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {4} * I19N1 =  Ideal.span {B.equivFun.symm ![144, -203, -111, -59, -29]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E19RS1 
