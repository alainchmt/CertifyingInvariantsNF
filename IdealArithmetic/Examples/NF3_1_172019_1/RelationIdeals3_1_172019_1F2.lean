import IdealArithmetic.Examples.NF3_1_172019_1.PrimesBelow3_1_172019_1F2
import IdealArithmetic.Examples.NF3_1_172019_1.ClassGroupData3_1_172019_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 49 ![![83, 0, 0], ![19, 1, 0]]
  ![-527, 90, -3] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![4067, 0, 0], ![931, 49, 0]]
    hsu := by decide
    w := ![![-25823, 4410, -147], ![10192, -2450, 147]]
    hw := by decide
    g := ![![![-6762517, -947086342, 47371220], ![-16568079, -2321189900, 0]], ![![-1527661, -213950239, 10701330], ![-3742741, -524365209, 0]]]
    h := ![![![-3460, -199, -1], ![15087, 80, 0]], ![![1338, 69, 0], ![-5834, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {49} * I83N0 =  Ideal.span {B.equivFun.symm ![-527, 90, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 49 ![![83, 0, 0], ![23, 1, 0]]
  ![3183, 573, -122] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![4067, 0, 0], ![1127, 49, 0]]
    hsu := by decide
    w := ![![155967, 28077, -5978], ![-77812, -13279, 2891]]
    hw := by decide
    g := ![![![-203, -2251, 92], ![45, -5253, 0]], ![![-63, -654, 25], ![48, -1503, 0]]]
    h := ![![![2136032, 103927, 479], ![-7708151, -39879, 0]], ![![-1065618, -51870, -240], ![3845422, 19979, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {49} * I83N1 =  Ideal.span {B.equivFun.symm ![3183, 573, -122]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 49 ![![83, 0, 0], ![40, 1, 0]]
  ![165161, 79098, 11348] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![4067, 0, 0], ![1960, 49, 0]]
    hsu := by decide
    w := ![![8092889, 3875802, 556052], ![-1986852, -951531, -136514]]
    hw := by decide
    g := ![![![251, 1354, -72], ![-48, 3312, 0]], ![![112, 759, -40], ![-30, 1854, 0]]]
    h := ![![![1613227, 51165, 385], ![-3343317, -20607, 0]], ![![-396076, -12581, -95], ![820844, 5099, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {49} * I83N2 =  Ideal.span {B.equivFun.symm ![165161, 79098, 11348]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS2 


noncomputable def E103RS1 : RelationCertificate Table 49 ![![103, 0, 0], ![-17, 1, 0]]
  ![-33, -27, -4] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![5047, 0, 0], ![-833, 49, 0]]
    hsu := by decide
    w := ![![-1617, -1323, -196], ![196, 343, 49]]
    hw := by decide
    g := ![![![-2719551, -380875543, 19050576], ![-6662909, -933478225, 0]], ![![423621, 59325779, -2967348], ![1037873, 145400052, 0]]]
    h := ![![![-27896, 1691, -3], ![-169015, 305, 0]], ![![3404, -200, 0], ![20624, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {49} * I103N1 =  Ideal.span {B.equivFun.symm ![-33, -27, -4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS1 


noncomputable def E113RS1 : RelationCertificate Table 49 ![![113, 0, 0], ![-38, 1, 0]]
  ![-2817, -866, 153] ![![49, 0, 0], ![-20, 1, 0]] where
    su := ![![5537, 0, 0], ![-1862, 49, 0]]
    hsu := by decide
    w := ![![-138033, -42434, 7497], ![74088, 20776, -3773]]
    hw := by decide
    g := ![![![563, 12455, -573], ![62, 29887, 0]], ![![-138, -3985, 186], ![12, -9595, 0]]]
    h := ![![![-4479, 123, 1], ![-13245, 40, 0]], ![![2440, -48, -1], ![7216, 36, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {49} * I113N1 =  Ideal.span {B.equivFun.symm ![-2817, -866, 153]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E113RS1 
