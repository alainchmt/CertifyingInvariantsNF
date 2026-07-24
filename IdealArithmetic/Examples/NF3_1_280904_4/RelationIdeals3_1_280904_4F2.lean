import IdealArithmetic.Examples.NF3_1_280904_4.PrimesBelow3_1_280904_4F2
import IdealArithmetic.Examples.NF3_1_280904_4.ClassGroupData3_1_280904_4

set_option linter.all false

noncomputable section


noncomputable def E89RS0 : RelationCertificate Table 7 ![![89, 0, 0], ![16, 1, 0]]
  ![36, 3, -2] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![623, 0, 0], ![112, 7, 0]]
    hsu := by decide
    w := ![![252, 21, -14], ![273, 56, 0]]
    hw := by decide
    g := ![![![2, 114, 108], ![21, -386, 0]], ![![3, 22, 22], ![8, -78, 0]]]
    h := ![![![-459, -7806, -976], ![-159, 43431, 0]], ![![-496, -8430, -1054], ![-170, 46903, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {7} * I89N0 =  Ideal.span {B.equivFun.symm ![36, 3, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 7 ![![89, 0, 0], ![25, 1, 0]]
  ![46, -9, -8] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![623, 0, 0], ![175, 7, 0]]
    hsu := by decide
    w := ![![322, -63, -56], ![875, 84, -42]]
    hw := by decide
    g := ![![![462, 18, 122], ![141, -352, 0]], ![![107, 10, 34], ![35, -102, 0]]]
    h := ![![![-15103, -441846, -35356], ![-9165, 1573338, 0]], ![![-40816, -1194545, -95586], ![-24833, 4253574, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {7} * I89N1 =  Ideal.span {B.equivFun.symm ![46, -9, -8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 7 ![![89, 0, 0], ![-42, 1, 0]]
  ![-1983, 274, -94] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![623, 0, 0], ![-294, 7, 0]]
    hsu := by decide
    w := ![![-13881, 1918, -658], ![5614, -777, 266]]
    hw := by decide
    g := ![![![-163905, -370498, -384746], ![-99752, 1346622, 0]], ![![75848, 171459, 178054], ![46168, -623194, 0]]]
    h := ![![![4105, -270486, 12882], ![-4904, -573296, 0]], ![![-1642, 109395, -5210], ![2022, 231864, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {7} * I89N2 =  Ideal.span {B.equivFun.symm ![-1983, 274, -94]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS2 


noncomputable def E97RS0 : RelationCertificate Table 49 ![![97, 0, 0], ![27, 1, 0]]
  ![164, -19, 8] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![4753, 0, 0], ![1323, 49, 0]]
    hsu := by decide
    w := ![![8036, -931, 392], ![1813, -196, 98]]
    hw := by decide
    g := ![![![-90, -1519, -190], ![-14, 4652, 0]], ![![-31, -432, -54], ![13, 1322, 0]]]
    h := ![![![123509, 3894304, 288524], ![74563, -13993410, 0]], ![![27844, 878217, 65066], ![16847, -3155700, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {49} * I97N0 =  Ideal.span {B.equivFun.symm ![164, -19, 8]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 7 ![![97, 0, 0], ![-17, 1, 0]]
  ![270, 5, -22] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![679, 0, 0], ![-119, 7, 0]]
    hsu := by decide
    w := ![![1890, 35, -154], ![2723, 434, -56]]
    hw := by decide
    g := ![![![15365, 43825, 44606], ![10652, -156783, 0]], ![![1414, 1152, 1400], ![569, -4751, 0]]]
    h := ![![![-95594, 1727997, -203336], ![34641, 9861785, 0]], ![![-137391, 2483442, -292230], ![49755, 14173151, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {7} * I97N1 =  Ideal.span {B.equivFun.symm ![270, 5, -22]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS1 


noncomputable def E101RS0 : RelationCertificate Table 7 ![![101, 0, 0], ![34, 1, 0]]
  ![-360, -93, -8] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![707, 0, 0], ![238, 7, 0]]
    hsu := by decide
    w := ![![-2520, -651, -56], ![-21, -490, -210]]
    hw := by decide
    g := ![![![-6117, 1475, 8], ![-1536, -1143, 0]], ![![-1760, 444, 22], ![-432, -399, 0]]]
    h := ![![![-5406, -230547, -13564], ![-4098, 684978, 0]], ![![305, 14247, 838], ![339, -42334, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {7} * I101N0 =  Ideal.span {B.equivFun.symm ![-360, -93, -8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 7 ![![101, 0, 0], ![-21, 1, 0]]
  ![1105, -738, -418] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![707, 0, 0], ![-147, 7, 0]]
    hsu := by decide
    w := ![![7735, -5166, -2926], ![42854, 2555, -2730]]
    hw := by decide
    g := ![![![-1036140, 679724, 404932], ![-198936, -1637457, 0]], ![![276840, -147094, -75782], ![58091, 321555, 0]]]
    h := ![![![-2203, 50990, -4862], ![1034, 245322, 0]], ![![-11906, 274213, -26124], ![5259, 1319067, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {7} * I101N1 =  Ideal.span {B.equivFun.symm ![1105, -738, -418]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 7 ![![101, 0, 0], ![-14, 1, 0]]
  ![-72238, -8289, 2880] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![707, 0, 0], ![-98, 7, 0]]
    hsu := by decide
    w := ![![-505666, -58023, 20160], ![-437885, -108976, -7938]]
    hw := by decide
    g := ![![![152144810, -28227364, 7748202], ![39437467, -924, 0]], ![![-28368503, 5263209, -1444696], ![-7353395, 128, 0]]]
    h := ![![![17411763, -253276048, 36189270], ![-4921171, -1827556695, 0]], ![![15021479, -218506499, 31221186], ![-4245609, -1576670460, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {7} * I101N2 =  Ideal.span {B.equivFun.symm ![-72238, -8289, 2880]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS2 


noncomputable def E103RS1 : RelationCertificate Table 49 ![![103, 0, 0], ![-39, 1, 0]]
  ![533, -74, 26] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![5047, 0, 0], ![-1911, 49, 0]]
    hsu := by decide
    w := ![![26117, -3626, 1274], ![5880, -833, 294]]
    hw := by decide
    g := ![![![-348, -6652, -832], ![-218, 20383, 0]], ![![118, 2446, 306], ![111, -7497, 0]]]
    h := ![![![13100, -680629, 34910], ![-11515, -1797852, 0]], ![![2955, -153244, 7860], ![-2578, -404787, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {49} * I103N1 =  Ideal.span {B.equivFun.symm ![533, -74, 26]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 7 ![![107, 0, 0], ![-52, 1, 0]]
  ![-3979806, 550255, -188696] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![749, 0, 0], ![-364, 7, 0]]
    hsu := by decide
    w := ![![-27858642, 3851785, -1320872], ![11271547, -1558424, 534422]]
    hw := by decide
    g := ![![![-123415, -275822, -286060], ![-74659, 1001031, 0]], ![![58215, 129959, 134784], ![35205, -471690, 0]]]
    h := ![![![-72980270, 6138168427, -236118336], ![92833222, 12632236628, 0]], ![![29527707, -2483489825, 95532974], ![-37560029, -5110975936, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {7} * I107N1 =  Ideal.span {B.equivFun.symm ![-3979806, 550255, -188696]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 7 ![![109, 0, 0], ![31, 1, 0]]
  ![71, 10, -2] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![763, 0, 0], ![217, 7, 0]]
    hsu := by decide
    w := ![![497, 70, -14], ![350, 105, 14]]
    hw := by decide
    g := ![![![107, -101, -70], ![21, 270, 0]], ![![22, -30, -22], ![9, 83, 0]]]
    h := ![![![-2430, -88429, -5706], ![-1485, 310976, 0]], ![![-1722, -62177, -4012], ![-997, 218655, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {7} * I109N1 =  Ideal.span {B.equivFun.symm ![71, 10, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 


noncomputable def E131RS1 : RelationCertificate Table 7 ![![131, 0, 0], ![51, 1, 0]]
  ![-78923, 10912, -3742] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![917, 0, 0], ![357, 7, 0]]
    hsu := by decide
    w := ![![-552461, 76384, -26194], ![223524, -30905, 10598]]
    hw := by decide
    g := ![![![-284, -62, -48], ![-84, 249, 0]], ![![-127, -28, -20], ![-39, 102, 0]]]
    h := ![![![-32772, -2228937, -87450], ![-29645, 5726104, 0]], ![![13207, 901820, 35382], ![12129, -2316764, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {7} * I131N1 =  Ideal.span {B.equivFun.symm ![-78923, 10912, -3742]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS1 


noncomputable def E131RS2 : RelationCertificate Table 49 ![![131, 0, 0], ![-58, 1, 0]]
  ![1798, 1089, 310] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![6419, 0, 0], ![-2842, 49, 0]]
    hsu := by decide
    w := ![![88102, 53361, 15190], ![-833, 17052, 7448]]
    hw := by decide
    g := ![![![-8811365929669, -174486396788702, -21827223391842], ![-6438127584957, 534766973128953, 0]], ![![3923636224002, 77697504863323, 9719501501796], ![2866850703035, -238127786807827, 0]]]
    h := ![![![-4081591, 352134222, -12143740], ![4495257, 795415125, 0]], ![![50329, -4340609, 149692], ![-55373, -9804750, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {49} * I131N2 =  Ideal.span {B.equivFun.symm ![1798, 1089, 310]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E131RS2 


noncomputable def E137RS1 : RelationCertificate Table 49 ![![137, 0, 0], ![-16, 1, 0]]
  ![-69, -116, -44] ![![49, 0, 0], ![16, 1, 0]] where
    su := ![![6713, 0, 0], ![-784, 49, 0]]
    hsu := by decide
    w := ![![-3381, -5684, -2156], ![3136, -1617, -980]]
    hw := by decide
    g := ![![![2579335, 51084064, 6390292], ![1884804, -156562588, 0]], ![![-184226, -3648867, -456448], ![-134574, 11183042, 0]]]
    h := ![![![1039, -16994, 2124], ![-194, -145516, 0]], ![![-972, 16220, -2028], ![355, 138908, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {49} * I137N1 =  Ideal.span {B.equivFun.symm ![-69, -116, -44]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E137RS1 
