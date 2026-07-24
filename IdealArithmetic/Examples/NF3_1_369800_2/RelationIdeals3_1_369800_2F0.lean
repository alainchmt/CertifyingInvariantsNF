import IdealArithmetic.Examples.NF3_1_369800_2.PrimesBelow3_1_369800_2F0
import IdealArithmetic.Examples.NF3_1_369800_2.ClassGroupData3_1_369800_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![-46, -4, 1]]
  ![-1311, -371, -56] ![![2, 0, 0], ![-45, -4, 1]] where
    su := ![![4, 0, 0], ![-92, -8, 2]]
    hsu := by decide
    w := ![![-2622, -742, -112], ![1266, 358, 54]]
    hw := by decide
    g := ![![![0, 28, -5], ![83, 0, -3]], ![![103, -364, 72], ![-1521, 0, 60]]]
    h := ![![![2473, 85, -96], ![129, -1, 0]], ![![-1180, -36, 46], ![-44, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![-1311, -371, -56]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![-45, -4, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-45, -4, 1]] where
    su := ![![2, 0, 0], ![-45, -4, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-45, -4, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![32, 30, -6], ![101, 0, -4]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![32, 30, -6], ![101, 0, -4]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 98 ![![5, 0, 0], ![-2, 1, 0]]
  ![-191, -29, 6] ![![98, 0, 0], ![-69, -4, 1]] where
    su := ![![490, 0, 0], ![-196, 98, 0]]
    hsu := by decide
    w := ![![-18718, -2842, 588], ![-2842, 196, 0]]
    hw := by decide
    g := ![![![-3175377685412, 61783212203, 80108433901], ![2234020774397, 1440663901206, -5874]], ![![1058455737176, -20594336131, -26702723221], ![-744671135006, -480219716369, 1958]]]
    h := ![![![25284, -64452, 69048], ![-23003, -172617, 0]], ![![4299, -10954, 11736], ![-3908, -29340, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {98} * I5N0 =  Ideal.span {B.equivFun.symm ![-191, -29, 6]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 49 ![![7, 0, 0], ![-47, -6, 1]]
  ![-4824, -725, 150] ![![49, 0, 0], ![-24, 1, 0]] where
    su := ![![343, 0, 0], ![-2303, -294, 49]]
    hsu := by decide
    w := ![![-236376, -35525, 7350], ![164101, 23226, -4900]]
    hw := by decide
    g := ![![![-80, 163, -20], ![48, 390, 0]], ![![392, -867, 101], ![-161, -2025, 0]]]
    h := ![![![-11, -17, 7], ![101, 0, 0]], ![![42, 12, -5], ![-65, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {49} * I7N0 =  Ideal.span {B.equivFun.symm ![-4824, -725, 150]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![-3, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![-3, 1, 0]] where
    su := ![![7, 0, 0], ![-3, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![-3, 1, 0]]
    hw := by decide
    g := ![![![-2, 17, -12], ![7, 42, 0]], ![![3, -9, 6], ![1, -21, 0]]]
    h := ![![![-2, 17, -12], ![7, 42, 0]], ![![3, -9, 6], ![1, -21, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS1 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![-4, 1, 0]]
  ![7, 1, 0] ![![2, 0, 0], ![-45, -4, 1]] where
    su := ![![22, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![14, 2, 0], ![8, -2, 0]]
    hw := by decide
    g := ![![![1202, -4564, 883], ![-16901, 0, 688]], ![![-289, 1142, -221], ![4225, 0, -172]]]
    h := ![![![82, -414, 210], ![-65, -1155, 0]], ![![51, -249, 126], ![-34, -693, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![7, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 2 ![![11, 0, 0], ![-2, 1, 0]]
  ![-351, -25, 7] ![![2, 0, 0], ![-46, -3, 1]] where
    su := ![![22, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-702, -50, 14], ![2572, 330, -72]]
    hw := by decide
    g := ![![![47, -132, -41], ![29, 0, 0]], ![![22, -149, -45], ![31, 0, 0]]]
    h := ![![![2769, -5885, 5977], ![-1030, -32870, 0]], ![![-10019, 21315, -21646], ![3770, 119035, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {2} * I11N2 =  Ideal.span {B.equivFun.symm ![-351, -25, 7]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 49 ![![13, 0, 0], ![-52, -2, 1]]
  ![26, 55, -8] ![![49, 0, 0], ![-24, 1, 0]] where
    su := ![![637, 0, 0], ![-2548, -98, 49]]
    hsu := by decide
    w := ![![1274, 2695, -392], ![-3185, -1862, 294]]
    hw := by decide
    g := ![![![12492, -488527, 40738], ![-16084, -998080, 0]], ![![-76887, 3007496, -250793], ![99037, 6144430, 0]]]
    h := ![![![22, 5, -1], ![5, 0, 0]], ![![19, -2, 0], ![6, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {49} * I13N0 =  Ideal.span {B.equivFun.symm ![26, 55, -8]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 7 ![![13, 0, 0], ![3, 1, 0]]
  ![31, 12, -2] ![![7, 0, 0], ![-3, 1, 0]] where
    su := ![![91, 0, 0], ![21, 7, 0]]
    hsu := by decide
    w := ![![217, 84, -14], ![-735, -147, 28]]
    hw := by decide
    g := ![![![-10, -29, 14], ![7, -52, 0]], ![![-20, -14, 2], ![12, -11, 0]]]
    h := ![![![-1643, -5422, -3656], ![-791, 23763, 0]], ![![5682, 18764, 12652], ![2755, -82236, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {7} * I13N1 =  Ideal.span {B.equivFun.symm ![31, 12, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 14 ![![17, 0, 0], ![8, 1, 0]]
  ![-115, -33, -5] ![![14, 0, 0], ![-44, -3, 1]] where
    su := ![![238, 0, 0], ![112, 14, 0]]
    hsu := by decide
    w := ![![-1610, -462, -70], ![-1722, -476, -70]]
    hw := by decide
    g := ![![![-345856, -81347, -19952], ![1103009, 164736, 0]], ![![-171151, -40260, -9876], ![545943, 81536, 0]]]
    h := ![![![305, 3956, 995], ![395, -8460, 0]], ![![332, 4235, 1065], ![411, -9055, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {14} * I17N0 =  Ideal.span {B.equivFun.symm ![-115, -33, -5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 14 ![![17, 0, 0], ![-7, 1, 0]]
  ![-1079, -305, -46] ![![14, 0, 0], ![-41, -4, 1]] where
    su := ![![238, 0, 0], ![-98, 14, 0]]
    hsu := by decide
    w := ![![-15106, -4270, -644], ![-3262, -924, -140]]
    hw := by decide
    g := ![![![-6189402454685, -325081844615, -10900948656], ![18218209076679, 2580799420530, 5700]], ![![2063134196849, 108360617251, 3633649631], ![-6072736492080, -860266492380, -1900]]]
    h := ![![![-4280, 41382, -11902], ![4209, 101144, 0]], ![![-920, 8935, -2570], ![919, 21840, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {14} * I17N1 =  Ideal.span {B.equivFun.symm ![-1079, -305, -46]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 7 ![![17, 0, 0], ![-2, 1, 0]]
  ![33853, 9580, 1446] ![![7, 0, 0], ![-3, 1, 0]] where
    su := ![![119, 0, 0], ![-14, 7, 0]]
    hsu := by decide
    w := ![![236971, 67060, 10122], ![380863, 107779, 16268]]
    hw := by decide
    g := ![![![8155, -30878, 21374], ![-7902, -74880, 0]], ![![-1236, 3375, -2366], ![1020, 8320, 0]]]
    h := ![![![-1702233, 3480483, -3503658], ![405001, 29781816, 0]], ![![-2735853, 5593881, -5631128], ![650920, 47865750, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {7} * I17N2 =  Ideal.span {B.equivFun.symm ![33853, 9580, 1446]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS2 


noncomputable def E19RS0 : RelationCertificate Table 98 ![![19, 0, 0], ![-9, 1, 0]]
  ![1965, 167, -43] ![![98, 0, 0], ![-44, -3, 1]] where
    su := ![![1862, 0, 0], ![-882, 98, 0]]
    hsu := by decide
    w := ![![192570, 16366, -4214], ![1274, -784, 98]]
    hw := by decide
    g := ![![![440, 39, -6], ![-85, -142, 0]], ![![-89, -8, 1], ![157, 49, 0]]]
    h := ![![![-787, 12431, -2775], ![1047, 26341, 0]], ![![0, 111, -25], ![25, 238, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {98} * I19N0 =  Ideal.span {B.equivFun.symm ![1965, 167, -43]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 98 ![![19, 0, 0], ![-8, 1, 0]]
  ![677, 307, -50] ![![98, 0, 0], ![-69, -4, 1]] where
    su := ![![1862, 0, 0], ![-784, 98, 0]]
    hsu := by decide
    w := ![![66346, 30086, -4900], ![107898, 2156, -1372]]
    hw := by decide
    g := ![![![-43422765158909033, 844875281891642, 1095469618050521], ![30549864943420555, 19700841073202284, -22338]], ![![14474255843339141, -281625109342058, -365156559289613], ![-10183288870533880, -6566947382990135, 7446]]]
    h := ![![![-302977, 3449104, -866342], ![309123, 8230224, 0]], ![![-525368, 5980652, -1502216], ![535994, 14271045, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {98} * I19N1 =  Ideal.span {B.equivFun.symm ![677, 307, -50]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 49 ![![19, 0, 0], ![-3, 1, 0]]
  ![237, 66, 10] ![![49, 0, 0], ![-24, 1, 0]] where
    su := ![![931, 0, 0], ![-147, 49, 0]]
    hsu := by decide
    w := ![![11613, 3234, 490], ![-2352, -637, -98]]
    hw := by decide
    g := ![![![-409113, 16003220, -1334498], ![527018, 32695200, 0]], ![![55921, -2187330, 182400], ![-72025, -4468800, 0]]]
    h := ![![![-63072, 197835, -132602], ![20373, 1259724, 0]], ![![12793, -40122, 26892], ![-4120, -255475, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {49} * I19N2 =  Ideal.span {B.equivFun.symm ![237, 66, 10]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS2 


noncomputable def E23RS1 : RelationCertificate Table 49 ![![23, 0, 0], ![4, 1, 0]]
  ![-4147, -418, 100] ![![49, 0, 0], ![-24, 1, 0]] where
    su := ![![1127, 0, 0], ![196, 49, 0]]
    hsu := by decide
    w := ![![-203203, -20482, 4900], ![131810, 12985, -3136]]
    hw := by decide
    g := ![![![-512485, 20049998, -1671948], ![660216, 40962852, 0]], ![![-99382, 3891125, -324472], ![128136, 7949664, 0]]]
    h := ![![![1117291, 4730734, 2374076], ![399996, -27301824, 0]], ![![-725026, -3069834, -1540568], ![-259553, 17716500, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {49} * I23N1 =  Ideal.span {B.equivFun.symm ![-4147, -418, 100]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 14 ![![29, 0, 0], ![13, 1, 0]]
  ![-246, -4, 3] ![![14, 0, 0], ![-44, -3, 1]] where
    su := ![![406, 0, 0], ![182, 14, 0]]
    hsu := by decide
    w := ![![-3444, -56, 42], ![7182, 588, -154]]
    hw := by decide
    g := ![![![-405561, -95387, -23397], ![1293515, 193188, 0]], ![![-208735, -49093, -12042], ![665779, 99435, 0]]]
    h := ![![![-20258, -394504, -60813], ![-22658, 881790, 0]], ![![41911, 816676, 125891], ![46963, -1825425, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {14} * I29N1 =  Ideal.span {B.equivFun.symm ![-246, -4, 3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 98 ![![31, 0, 0], ![15, 1, 0]]
  ![121, 43, 8] ![![98, 0, 0], ![-69, -4, 1]] where
    su := ![![3038, 0, 0], ![1470, 98, 0]]
    hsu := by decide
    w := ![![11858, 4214, 784], ![-3332, -1078, -196]]
    hw := by decide
    g := ![![![-217357463925, 4229329694, 5483565563], ![152920727206, 98615659685, 267300]], ![![-108678731984, 2114664847, 2741782782], ![76460363610, 49307829850, 133650]]]
    h := ![![![-210131, -5068017, -676876], ![-265160, 10491582, 0]], ![![59096, 1425653, 190408], ![74621, -2951325, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {98} * I31N1 =  Ideal.span {B.equivFun.symm ![121, 43, 8]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS1 
