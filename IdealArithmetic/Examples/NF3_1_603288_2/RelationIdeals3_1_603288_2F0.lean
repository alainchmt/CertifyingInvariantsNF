import IdealArithmetic.Examples.NF3_1_603288_2.PrimesBelow3_1_603288_2F0
import IdealArithmetic.Examples.NF3_1_603288_2.ClassGroupData3_1_603288_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 128 ![![2, 0, 0], ![14, 1, 1]]
  ![-4, -1, 0] ![![128, 0, 0], ![29, 62, 1]] where
    su := ![![256, 0, 0], ![1792, 128, 128]]
    hsu := by decide
    w := ![![-512, -128, 0], ![-256, -256, -128]]
    hw := by decide
    g := ![![![-16830, 3443, 0], ![-2041, 0, 255]], ![![-100832, 20971, 6], ![-12893, -1, 1530]]]
    h := ![![![572, -2127, -979], ![2468, -255, 0]], ![![566, -2128, -980], ![2469, -255, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {128} * I2N0 =  Ideal.span {B.equivFun.symm ![-4, -1, 0]} * (J0 ^ 13*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_13J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![15, 1, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![15, 1, 1]] where
    su := ![![2, 0, 0], ![15, 1, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![15, 1, 1]]
    hw := by decide
    g := ![![![-9, 39, -16], ![20, 0, -2]], ![![5, 278, -107], ![131, 0, -14]]]
    h := ![![![-9, 39, -16], ![20, 0, -2]], ![![5, 278, -107], ![131, 0, -14]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 8 ![![3, 0, 0], ![-1, 1, 0]]
  ![-4, 1, 0] ![![8, 0, 0], ![13, 2, 1]] where
    su := ![![24, 0, 0], ![-8, 8, 0]]
    hsu := by decide
    w := ![![-32, 8, 0], ![88, -16, 0]]
    hw := by decide
    g := ![![![-1846, 70, 552], ![-2911, 0, 188]], ![![-10, -2, -1], ![9, 0, 0]]]
    h := ![![![-2, 2, -2], ![-2, 3, 0]], ![![8, -5, 0], ![13, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {8} * I3N0 =  Ideal.span {B.equivFun.symm ![-4, 1, 0]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 256 ![![5, 0, 0], ![0, 1, 0]]
  ![-4, -1, 0] ![![1280, 0, 0], ![-4865, -406, -309]] where
    su := ![![1280, 0, 0], ![0, 256, 0]]
    hsu := by decide
    w := ![![-5120, -1280, 0], ![62720, 0, 2048]]
    hw := by decide
    g := ![![![551, 46, 35], ![145, 0, 0]], ![![3353, 288, 216], ![900, -2, 0]]]
    h := ![![![-4, -1, 0], ![0, 0, 0]], ![![49, 0, 0], ![0, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {256} * I5N0 =  Ideal.span {B.equivFun.symm ![-4, -1, 0]} * (J0 ^ 13*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_13J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 200 ![![5, 0, 0], ![16, 0, 1]]
  ![88, 10, 3] ![![200, 0, 0], ![85, 6, 1]] where
    su := ![![1000, 0, 0], ![3200, 0, 200]]
    hsu := by decide
    w := ![![17600, 2000, 600], ![11400, 1000, 400]]
    hw := by decide
    g := ![![![1488209, 788258, 148209], ![656989, -2524899, 0]], ![![4759381, 2520869, 473976], ![2100924, -8074677, 0]]]
    h := ![![![-8, 2, -1], ![8, 0, 0]], ![![-11, 1, -1], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {200} * I5N1 =  Ideal.span {B.equivFun.symm ![88, 10, 3]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 800 ![![7, 0, 0], ![0, 1, 0]]
  ![84, 5, 4] ![![800, 0, 0], ![-35, 14, 1]] where
    su := ![![5600, 0, 0], ![0, 800, 0]]
    hsu := by decide
    w := ![![67200, 4000, 3200], ![5600, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![1, 0, 0]], ![![10, -4, 1], ![100, -32, 0]]]
    h := ![![![12, 0, 0], ![5, 2, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {800} * I7N0 =  Ideal.span {B.equivFun.symm ![84, 5, 4]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 1280 ![![11, 0, 0], ![17, -3, 1]]
  ![548, 45, 18] ![![1280, 0, 0], ![-4865, -406, -309]] where
    su := ![![14080, 0, 0], ![21760, -3840, 1280]]
    hsu := by decide
    w := ![![701440, 57600, 23040], ![-5635840, -385280, -176640]]
    hw := by decide
    g := ![![![12746286625, -19211753501, -6688859480], ![-40737382637, 4958377538, 56318]], ![![19119431189, -28817630151, -10033289142], ![-61106073635, 7437566308, 84477]]]
    h := ![![![5, 12, -1], ![29, 0, 0]], ![![-136, -74, 3], ![-171, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {1280} * I11N0 =  Ideal.span {B.equivFun.symm ![548, 45, 18]} * (J0 ^ 13*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_13J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 200 ![![11, 0, 0], ![-5, 1, 0]]
  ![4, 5, -1] ![![200, 0, 0], ![85, 6, 1]] where
    su := ![![2200, 0, 0], ![-1000, 200, 0]]
    hsu := by decide
    w := ![![800, 1000, -200], ![200, 400, 0]]
    hw := by decide
    g := ![![![-2949992, -1562455, -293774], ![-1301921, 5004727, 0]], ![![1069741, 566602, 106533], ![472211, -1814901, 0]]]
    h := ![![![104, 2977, -1199], ![228, 6594, 0]], ![![1, 0, 0], ![2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {200} * I11N1 =  Ideal.span {B.equivFun.symm ![4, 5, -1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E11RS1 


noncomputable def E17RS0 : RelationCertificate Table 640 ![![17, 0, 0], ![1, 1, 0]]
  ![-52, 15, -2] ![![640, 0, 0], ![285, 62, 1]] where
    su := ![![10880, 0, 0], ![640, 640, 0]]
    hsu := by decide
    w := ![![-33280, 9600, -1280], ![-30080, 3200, 1280]]
    hw := by decide
    g := ![![![3846620, -11450842, -4435417], ![596949, 24370080, -696288]], ![![240349, -715692, -277214], ![37453, 1523131, -43518]]]
    h := ![![![-4, -4, -8], ![16, 67, 0]], ![![-3, -3, -6], ![4, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {640} * I17N0 =  Ideal.span {B.equivFun.symm ![-52, 15, -2]} * (J0 ^ 11*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 1280 ![![17, 0, 0], ![6, 1, 0]]
  ![264, 20, 9] ![![1280, 0, 0], ![285, 126, 1]] where
    su := ![![21760, 0, 0], ![7680, 1280, 0]]
    hsu := by decide
    w := ![![337920, 25600, 11520], ![236800, 15360, 7680]]
    hw := by decide
    g := ![![![-47, -18, 3], ![217, -16, 0]], ![![-111, -48, 1], ![502, -7, 0]]]
    h := ![![![252, 42, 1], ![-670, -4, 0]], ![![175, 27, 0], ![-465, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {1280} * I17N1 =  Ideal.span {B.equivFun.symm ![264, 20, 9]} * (J0 ^ 14*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_14J1_1 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 80 ![![17, 0, 0], ![-7, 1, 0]]
  ![-52, -5, -2] ![![80, 0, 0], ![45, 6, 1]] where
    su := ![![1360, 0, 0], ![-560, 80, 0]]
    hsu := by decide
    w := ![![-4160, -400, -160], ![-4720, -320, -160]]
    hw := by decide
    g := ![![![-101722832, -18574708, -10787840], ![-58746947, 76716628, 48942]], ![![33907577, 6191565, 3595946], ![19582377, -25572210, -16314]]]
    h := ![![![-148, 27, -2], ![-352, 16, 0]], ![![-176, 31, -2], ![-419, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {80} * I17N2 =  Ideal.span {B.equivFun.symm ![-52, -5, -2]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E17RS2 


noncomputable def E19RS0 : RelationCertificate Table 400 ![![19, 0, 0], ![1, 1, 0]]
  ![-104, 20, 1] ![![400, 0, 0], ![-35, 14, 1]] where
    su := ![![7600, 0, 0], ![400, 400, 0]]
    hsu := by decide
    w := ![![-41600, 8000, 400], ![8400, -2800, 400]]
    hw := by decide
    g := ![![![8634694, -3453879, 1744379], ![-871985, -24888559, 0]], ![![1581959, -632784, 319580], ![-159403, -4559736, 0]]]
    h := ![![![-12, -6, -1], ![124, 10, 0]], ![![2, 0, -1], ![-17, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {400} * I19N0 =  Ideal.span {B.equivFun.symm ![-104, 20, 1]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 12800 ![![19, 0, 0], ![9, 1, 0]]
  ![-1868, -135, -58] ![![12800, 0, 0], ![-61205, -3278, -4441]] where
    su := ![![243200, 0, 0], ![115200, 12800, 0]]
    hsu := by decide
    w := ![![-23910400, -1728000, -742400], ![224883200, 15833600, 7321600]]
    hw := by decide
    g := ![![![-979860024799061, 1958831230618966, 1115503381790124], ![3796666681670319, -393922195568104, -14591970]], ![![-522592013168592, 1044709989666562, 594935136958928], ![2024888896902937, -210091837636328, -7782384]]]
    h := ![![![-67181144, -11807009, -964990], ![141826652, 9167376, 0]], ![![631701991, 111030739, 9075956], ![-1333591140, -86221296, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {12800} * I19N1 =  Ideal.span {B.equivFun.symm ![-1868, -135, -58]} * (J0 ^ 13*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_13J1_2 E19RS1 


noncomputable def E31RS1 : RelationCertificate Table 64 ![![31, 0, 0], ![2, 1, 0]]
  ![68, 5, 2] ![![64, 0, 0], ![29, 30, 1]] where
    su := ![![1984, 0, 0], ![128, 64, 0]]
    hsu := by decide
    w := ![![4352, 320, 128], ![11072, 960, 384]]
    hw := by decide
    g := ![![![10488083, -3135305, -28476], ![3282319, 0, -182482]], ![![911984, -272659, -2477], ![285470, 0, -15868]]]
    h := ![![![8068, 4049, 16], ![-125020, -247, 0]], ![![20533, 10308, 44], ![-318175, -679, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {64} * I31N1 =  Ideal.span {B.equivFun.symm ![68, 5, 2]} * (J0 ^ 11*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_0 E31RS1 
