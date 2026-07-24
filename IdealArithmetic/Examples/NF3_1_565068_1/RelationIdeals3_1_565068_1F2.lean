import IdealArithmetic.Examples.NF3_1_565068_1.PrimesBelow3_1_565068_1F2
import IdealArithmetic.Examples.NF3_1_565068_1.ClassGroupData3_1_565068_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 363 ![![83, 0, 0], ![11, 1, 0]]
  ![-222, 17, -4] ![![363, 0, 0], ![112, 1, 0]] where
    su := ![![30129, 0, 0], ![3993, 363, 0]]
    hsu := by decide
    w := ![![-80586, 6171, -1452], ![-24684, 1815, -363]]
    hw := by decide
    g := ![![![-959, 1192345, 52759], ![3107, -3830304, 0]], ![![-208, 172052, 7613], ![674, -552704, 0]]]
    h := ![![![18, -15293, -6373], ![-156, 105791, 0]], ![![-4, -4685, -1952], ![24, 32403, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {363} * I83N1 =  Ideal.span {B.equivFun.symm ![-222, 17, -4]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 33 ![![89, 0, 0], ![35, 1, 0]]
  ![-4794, 49, -161] ![![33, 0, 0], ![13, 1, 0]] where
    su := ![![2937, 0, 0], ![1155, 33, 0]]
    hsu := by decide
    w := ![![-158202, 1617, -5313], ![-55077, 561, -1848]]
    hw := by decide
    g := ![![![-212, 19355, 6919], ![532, -45664, 0]], ![![-83, 7833, 2800], ![208, -18480, 0]]]
    h := ![![![1150474, 32641, -34], ![-2925628, 573, 0]], ![![400489, 11347, -14], ![-1018434, 238, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {33} * I89N1 =  Ideal.span {B.equivFun.symm ![-4794, 49, -161]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 363 ![![101, 0, 0], ![-11, 1, 0]]
  ![-410028, 4167, -13778] ![![363, 0, 0], ![155, 0, 1]] where
    su := ![![36663, 0, 0], ![-3993, 363, 0]]
    hsu := by decide
    w := ![![-148840164, 1512621, -5001414], ![-63865857, 649044, -2146056]]
    hw := by decide
    g := ![![![-2093, 6600, 1], ![-626, -19020, 0]], ![![68, -614, -1], ![356, 1770, 0]]]
    h := ![![![-176504280, 16047329, -1043], ![-1620592932, 18313, 0]], ![![-75736251, 6885750, -447], ![-695380492, 7847, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {363} * I101N1 =  Ideal.span {B.equivFun.symm ![-410028, 4167, -13778]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 3 ![![103, 0, 0], ![27, 1, 0]]
  ![3, 6, 8] ![![3, 0, 0], ![20, 0, 1]] where
    su := ![![309, 0, 0], ![81, 3, 0]]
    hsu := by decide
    w := ![![9, 18, 24], ![-138, -126, -69]]
    hw := by decide
    g := ![![![429, -198, -298], ![2858, 0, 0]], ![![101, -49, -74], ![708, 0, 0]]]
    h := ![![![-33, -24, -4], ![126, 84, 0]], ![![182, 2, -1], ![-696, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {3} * I103N0 =  Ideal.span {B.equivFun.symm ![3, 6, 8]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 3 ![![103, 0, 0], ![-18, 1, 0]]
  ![2559, -26, 86] ![![3, 0, 0], ![20, 0, 1]] where
    su := ![![309, 0, 0], ![-54, 3, 0]]
    hsu := by decide
    w := ![![7677, -78, 258], ![53124, -540, 1785]]
    hw := by decide
    g := ![![![-15, -10, 9], ![-1, 0, 0]], ![![0, -1, -2], ![0, 0, 0]]]
    h := ![![![137199, -7795, 52], ![784941, -1054, 0]], ![![949292, -53952, 365], ![5431076, -7400, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {3} * I103N1 =  Ideal.span {B.equivFun.symm ![2559, -26, 86]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 3 ![![103, 0, 0], ![-10, 1, 0]]
  ![6, 3, -2] ![![3, 0, 0], ![20, 0, 1]] where
    su := ![![309, 0, 0], ![-30, 3, 0]]
    hsu := by decide
    w := ![![18, 9, -6], ![-33, -9, 24]]
    hw := by decide
    g := ![![![-41, 18, 27], ![-260, 0, 0]], ![![-15, -2, -4], ![32, 0, 0]]]
    h := ![![![22, 5, -4], ![226, 82, 0]], ![![-27, 10, -4], ![-277, 84, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {3} * I103N2 =  Ideal.span {B.equivFun.symm ![6, 3, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E103RS2 


noncomputable def E107RS1 : RelationCertificate Table 121 ![![107, 0, 0], ![24, 1, 0]]
  ![6505028, -66105, 218585] ![![121, 0, 0], ![-9, 1, 0]] where
    su := ![![12947, 0, 0], ![2904, 121, 0]]
    hsu := by decide
    w := ![![787108388, -7998705, 26448785], ![-68381577, 694903, -2297790]]
    hw := by decide
    g := ![![![-11429, -18745930, 11717015], ![-153987, -283551704, 0]], ![![-8349, -13671074, 8545005], ![-112308, -206789088, 0]]]
    h := ![![![-5220764, 2644810128, 529008205], ![23546949, -11320731870, 0]], ![![453549, -229773041, -45958620], ![-2045620, 983510670, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {121} * I107N1 =  Ideal.span {B.equivFun.symm ![6505028, -66105, 218585]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E107RS1 


noncomputable def E113RS1 : RelationCertificate Table 363 ![![113, 0, 0], ![-3, 1, 0]]
  ![1466799, -14906, 49288] ![![363, 0, 0], ![112, 1, 0]] where
    su := ![![41019, 0, 0], ![-1089, 363, 0]]
    hsu := by decide
    w := ![![532448037, -5410878, 17891544], ![162063528, -1646931, 5445726]]
    hw := by decide
    g := ![![![130547975, -168212355416, -7443076152], ![-423115298, 540367328604, 0]], ![![-2183601, 2813504718, 124492222], ![7077207, -9038135308, 0]]]
    h := ![![![38945901, -12977924, 816], ![1466473338, -8584, 0]], ![![11854132, -3950147, 249], ![446356820, -2627, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {363} * I113N1 =  Ideal.span {B.equivFun.symm ![1466799, -14906, 49288]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E113RS1 


noncomputable def E127RS0 : RelationCertificate Table 33 ![![127, 0, 0], ![22, 1, 0]]
  ![-39, -26, -1] ![![33, 0, 0], ![23, 0, 1]] where
    su := ![![4191, 0, 0], ![726, 33, 0]]
    hsu := by decide
    w := ![![-1287, -858, -33], ![264, 165, -33]]
    hw := by decide
    g := ![![![-13543647, -2682179, 285773], ![-9430813, -14752000, 0]], ![![-2454793, -486145, 51796], ![-1709317, -2673800, 0]]]
    h := ![![![3651, 152, -3], ![-21078, 76, 0]], ![![-776, -49, -3], ![4480, 76, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {33} * I127N0 =  Ideal.span {B.equivFun.symm ![-39, -26, -1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 33 ![![127, 0, 0], ![29, 1, 0]]
  ![1902, -19, 64] ![![33, 0, 0], ![23, 0, 1]] where
    su := ![![4191, 0, 0], ![957, 33, 0]]
    hsu := by decide
    w := ![![62766, -627, 2112], ![45177, -462, 1518]]
    hw := by decide
    g := ![![![6517192, 1290686, -137520], ![4538167, 7098784, 0]], ![![1650448, 326862, -34827], ![1149290, 1797744, 0]]]
    h := ![![![1220688, 45371, 547], ![-5345706, -13881, 0]], ![![878603, 32652, 393], ![-3847628, -9973, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {33} * I127N1 =  Ideal.span {B.equivFun.symm ![1902, -19, 64]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 33 ![![127, 0, 0], ![-52, 1, 0]]
  ![-84, -1, -3] ![![33, 0, 0], ![23, 0, 1]] where
    su := ![![4191, 0, 0], ![-1716, 33, 0]]
    hsu := by decide
    w := ![![-2772, -33, -99], ![-1914, 33, -66]]
    hw := by decide
    g := ![![![-4479, -885, 94], ![-3103, -4870, 0]], ![![1789, 358, -39], ![1288, 1970, 0]]]
    h := ![![![-804, 56, -4], ![-1962, 101, 0]], ![![-518, 20, -1], ![-1264, 25, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {33} * I127N2 =  Ideal.span {B.equivFun.symm ![-84, -1, -3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS2 


noncomputable def E131RS1 : RelationCertificate Table 121 ![![131, 0, 0], ![25, 1, 0]]
  ![-12329, 126, -414] ![![121, 0, 0], ![-9, 1, 0]] where
    su := ![![15851, 0, 0], ![3025, 121, 0]]
    hsu := by decide
    w := ![![-1491809, 15246, -50094], ![129591, -1331, 4356]]
    hw := by decide
    g := ![![![812426, 1328943493, -830646102], ![10922633, 20101635672, 0]], ![![159451, 260818315, -163022520], ![2143734, 3945144984, 0]]]
    h := ![![![2240516, 89543, -19], ![-11740797, 415, 0]], ![![-194684, -7784, 1], ![1020187, -19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {121} * I131N1 =  Ideal.span {B.equivFun.symm ![-12329, 126, -414]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 11 ![![137, 0, 0], ![-43, 1, 0]]
  ![354944, -3607, 11927] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![1507, 0, 0], ![-473, 11, 0]]
    hsu := by decide
    w := ![![3904384, -39677, 131197], ![173173, -1760, 5819]]
    hw := by decide
    g := ![![![40, -1162, -1973], ![-93, 4384, 0]], ![![-21, 361, 622], ![40, -1380, 0]]]
    h := ![![![8104116, -199765, 1436], ![25811836, -36961, 0]], ![![359486, -8847, 62], ![1144973, -1593, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {11} * I137N1 =  Ideal.span {B.equivFun.symm ![354944, -3607, 11927]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E137RS1 
