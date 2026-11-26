import IdealArithmetic.Examples.NF5_1_48600000_1.PrimesBelow5_1_48600000_1F0
import IdealArithmetic.Examples.NF5_1_48600000_1.ClassGroupData5_1_48600000_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0, 0, 0], ![5, -5, 2, 1, 3]]
  ![-21, -3, -8, 7, 10] ![![2, 0, 0, 0, 0], ![2, 1, 1, 0, 0]] where
    su := ![![4, 0, 0, 0, 0], ![10, -10, 4, 2, 6]]
    hsu := by decide
    w := ![![-42, -6, -16, 14, 20], ![4, 22, -16, -12, -44]]
    hw := by decide
    g := ![![![26, -23, -8, -5, 2], ![13, 7, 0, 0, 0]], ![![-1493, 4927, 1176, 1949, 43], ![1563, -3864, 3, 0, 0]]]
    h := ![![![-4640859, -2429154, 886649, 1379684, 2275175], ![-539979, 736740, -8697, 0, 93]], ![![3606159, 1887569, -688973, -1072079, -1767923], ![419590, -572481, 6759, 0, -72]]]
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
  ![-2, 3, -3, -1, -5] ![![4, 0, 0, 0, 0], ![-2, -5, 0, 1, 2]] where
    su := ![![8, 0, 0, 0, 0], ![4, -12, 4, 4, 8]]
    hsu := by decide
    w := ![![-8, 12, -12, -4, -20], ![-12, 8, -16, 0, -12]]
    hw := by decide
    g := ![![![-329, 625, 260, 85, -30], ![274, 279, 0, 0, -53]], ![![543, -809, -324, -121, 45], ![-331, -378, 0, 0, 60]]]
    h := ![![![28779, 4410, 972, -4019, -2924], ![3328, -4991, 212, 0, 35]], ![![29263, 4486, 988, -4087, -2974], ![3383, -5075, 214, 0, 35]]]
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
  ![144, -203, -111, -59, -29] ![![4, 0, 0, 0, 0], ![-2, -5, 0, 1, 2]] where
    su := ![![76, 0, 0, 0, 0], ![24, 4, 0, 0, 0]]
    hsu := by decide
    w := ![![576, -812, -444, -236, -116], ![996, 128, 1880, 1024, 1416]]
    hw := by decide
    g := ![![![-5778276515821935720444, 2463980730040537880070, 966266749573504673414, 956604133117360525629, -19325562199971455903], ![38650597539649913593, 1932533828434692501228, -131715073245308, -4228, 0]], ![![-2063670184248704890680, 879993117882957080169, 345095267709268747087, 341644333260601380997, -6901986500078719791], ![13803784835767080484, 690190653021281479585, -47041097588216, -1510, 0]]]
    h := ![![![4881696, 876809, 3997643, 851683, 46657], ![-15384804, -182110, -15073896, -110814, 0]], ![![-7539483, -1354162, -6174868, -1315576, -72090], ![23760899, 281173, 23283620, 171258, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {4} * I19N1 =  Ideal.span {B.equivFun.symm ![144, -203, -111, -59, -29]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E19RS1 
