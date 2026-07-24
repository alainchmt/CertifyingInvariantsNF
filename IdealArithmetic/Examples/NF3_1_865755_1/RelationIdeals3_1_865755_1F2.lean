import IdealArithmetic.Examples.NF3_1_865755_1.PrimesBelow3_1_865755_1F2
import IdealArithmetic.Examples.NF3_1_865755_1.ClassGroupData3_1_865755_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 2 ![![83, 0, 0], ![3, 1, 0]]
  ![439, 2, -9] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![166, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![878, 4, -18], ![-2068, 92, 10]]
    hw := by decide
    g := ![![![2888, 25, 212], ![1457, 0, 0]], ![![686, 4, 43], ![345, 3, 0]]]
    h := ![![![-2360, -4737, -5923], ![-107, 98320, 0]], ![![5564, 11176, 13975], ![374, -231984, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {2} * I83N1 =  Ideal.span {B.equivFun.symm ![439, 2, -9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 32 ![![89, 0, 0], ![-22, 1, 0]]
  ![-841395, -175312, -49323] ![![32, 0, 0], ![-15, 1, 0]] where
    su := ![![2848, 0, 0], ![-704, 32, 0]]
    hsu := by decide
    w := ![![-26924640, -5609984, -1578336], ![-1490816, -310624, -87392]]
    hw := by decide
    g := ![![![-5471684, 51900356, -18582548], ![4186740, 118928565, 0]], ![![1346025, -12766290, 4570876], ![-1029863, -29253693, 0]]]
    h := ![![![2811609, -32358750, 7706273], ![-1058566, -137181524, 0]], ![![155688, -1791703, 426696], ![-58575, -7595735, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {32} * I89N1 =  Ideal.span {B.equivFun.symm ![-841395, -175312, -49323]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 4 ![![97, 0, 0], ![-47, 1, 0]]
  ![-950265, -197996, -55705] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![388, 0, 0], ![-188, 4, 0]]
    hsu := by decide
    w := ![![-3801060, -791984, -222820], ![-16887952, -3518752, -989980]]
    hw := by decide
    g := ![![![4000, -487, 5], ![879, 0, 0]], ![![-1939, 269, -35], ![-417, 15, 0]]]
    h := ![![![-172719518, 5540019791, -602334640], ![140802527, 11685280875, 0]], ![![-767385794, 24614078266, -2676147835], ![625579510, 51917218500, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {4} * I97N1 =  Ideal.span {B.equivFun.symm ![-950265, -197996, -55705]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS1 


noncomputable def E103RS0 : RelationCertificate Table 8 ![![103, 0, 0], ![48, 1, 0]]
  ![11787, 2456, 691] ![![8, 0, 0], ![1, 1, 0]] where
    su := ![![824, 0, 0], ![384, 8, 0]]
    hsu := by decide
    w := ![![94296, 19648, 5528], ![209488, 43648, 12280]]
    hw := by decide
    g := ![![![323, 28, -17], ![45, 0, 0]], ![![120, 25, 32], ![24, -61, 0]]]
    h := ![![![440445, 14765144, 1506997], ![348624, -31044000, 0]], ![![978470, 32802248, 3347945], ![774552, -68967360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {8} * I103N0 =  Ideal.span {B.equivFun.symm ![11787, 2456, 691]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 256 ![![103, 0, 0], ![-42, 1, 0]]
  ![1239, 80, -49] ![![256, 0, 0], ![-111, 1, 0]] where
    su := ![![26368, 0, 0], ![-10752, 256, 0]]
    hsu := by decide
    w := ![![317184, 20480, -12544], ![-151040, -9472, 5888]]
    hw := by decide
    g := ![![![669559675, -48241191899, 2192866457], ![-478758998, -112274762593, 0]], ![![-271680179, 19574328390, -889776692], ![194261329, 45556566629, 0]]]
    h := ![![![11539, -299533, 36537], ![-7573, -752672, 0]], ![![-5484, 142638, -17399], ![3633, 358424, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {256} * I103N1 =  Ideal.span {B.equivFun.symm ![1239, 80, -49]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 128 ![![103, 0, 0], ![-6, 1, 0]]
  ![-35, -16, 5] ![![128, 0, 0], ![17, 1, 0]] where
    su := ![![13184, 0, 0], ![-768, 128, 0]]
    hsu := by decide
    w := ![![-4480, -2048, 640], ![768, -128, 0]]
    hw := by decide
    g := ![![![2447, 22640, 6290], ![523, -161025, 0]], ![![-100, -900, -250], ![-1, 6400, 0]]]
    h := ![![![415, -1040, 1040], ![-11, -21423, 0]], ![![-68, 184, -185], ![102, 3811, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {128} * I103N2 =  Ideal.span {B.equivFun.symm ![-35, -16, 5]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E103RS2 


noncomputable def E107RS0 : RelationCertificate Table 64 ![![107, 0, 0], ![12, 1, 0]]
  ![191, 16, -9] ![![64, 0, 0], ![17, 1, 0]] where
    su := ![![6848, 0, 0], ![768, 64, 0]]
    hsu := by decide
    w := ![![12224, 1024, -576], ![768, 128, -64]]
    hw := by decide
    g := ![![![-10652532, -106546811, -29615843], ![-4494333, 379082790, 0]], ![![-4084237855, -40850662930, -11354885394], ![-1723167258, 145342533043, 0]]]
    h := ![![![-1345, -8895, -3422], ![-196, 73229, 0]], ![![-88, -554, -213], ![26, 4558, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {64} * I107N0 =  Ideal.span {B.equivFun.symm ![191, 16, -9]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 4 ![![107, 0, 0], ![19, 1, 0]]
  ![10405, 804, -455] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![428, 0, 0], ![76, 4, 0]]
    hsu := by decide
    w := ![![41620, 3216, -1820], ![-114932, -5732, 4020]]
    hw := by decide
    g := ![![![-620526, -93833, -38640], ![-178589, -289, 0]], ![![-207471, -31389, -12970], ![-59712, -55, 0]]]
    h := ![![![-4500580, -47197365, -11802245], ![-1240181, 252567952, 0]], ![![12433632, 130391346, 32605855], ![3426465, -697765096, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {4} * I107N1 =  Ideal.span {B.equivFun.symm ![10405, 804, -455]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 2 ![![107, 0, 0], ![-31, 1, 0]]
  ![939, -560, 161] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![214, 0, 0], ![-62, 2, 0]]
    hsu := by decide
    w := ![![1878, -1120, 322], ![44738, 6098, -2800]]
    hw := by decide
    g := ![![![1953021, -26140, -16772], ![963442, 65331, 0]], ![![-252967, 10209, 27482], ![-121377, -18788, 0]]]
    h := ![![![7592, -128233, 21378], ![-3339, -457457, 0]], ![![178601, -3022463, 503860], ![-79930, -10782884, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {2} * I107N2 =  Ideal.span {B.equivFun.symm ![939, -560, 161]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS2 


noncomputable def E109RS1 : RelationCertificate Table 4 ![![109, 0, 0], ![-21, 1, 0]]
  ![-12283, 316, 133] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![436, 0, 0], ![-84, 4, 0]]
    hsu := by decide
    w := ![![-49132, 1264, 532], ![25456, -6464, 1580]]
    hw := by decide
    g := ![![![1351662, 204629, 84937], ![389073, 0, 0]], ![![-52425, -7931, -3276], ![-15089, -15, 0]]]
    h := ![![![-7426249, 78383636, -19600838], ![2149892, 427298295, 0]], ![![3858242, -40723334, 10183395], ![-1116850, -221997932, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {4} * I109N1 =  Ideal.span {B.equivFun.symm ![-12283, 316, 133]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS1 


noncomputable def E127RS0 : RelationCertificate Table 8 ![![127, 0, 0], ![0, 1, 0]]
  ![-595, 120, -27] ![![8, 0, 0], ![1, 1, 0]] where
    su := ![![1016, 0, 0], ![0, 8, 0]]
    hsu := by decide
    w := ![![-4760, 960, -216], ![-7888, -1408, 600]]
    hw := by decide
    g := ![![![-8893, -1722, -531], ![-1323, 0, 0]], ![![-1160, -213, -32], ![-168, -61, 0]]]
    h := ![![![8925, 4465, 22324], ![100, -567035, 0]], ![![14790, 7397, 36995], ![63, -939658, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {8} * I127N0 =  Ideal.span {B.equivFun.symm ![-595, 120, -27]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 8 ![![127, 0, 0], ![43, 1, 0]]
  ![-25087, -3416, 1569] ![![8, 0, 0], ![1, 1, 0]] where
    su := ![![1016, 0, 0], ![344, 8, 0]]
    hsu := by decide
    w := ![![-200696, -27328, 12552], ![405832, 29272, -17080]]
    hw := by decide
    g := ![![![3249084, 628889, 193653], ![484751, 593, 0]], ![![1529181, 296001, 91188], ![228150, 205, 0]]]
    h := ![![![21317219, 555220042, 63103572], ![11589510, -1602830415, 0]], ![![-43148672, -1123831676, -127729155], ![-23458329, 3244320110, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {8} * I127N1 =  Ideal.span {B.equivFun.symm ![-25087, -3416, 1569]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 8 ![![127, 0, 0], ![-43, 1, 0]]
  ![-309, -16, 11] ![![8, 0, 0], ![1, 1, 0]] where
    su := ![![1016, 0, 0], ![-344, 8, 0]]
    hsu := by decide
    w := ![![-2472, -128, 88], ![2728, 88, -80]]
    hw := by decide
    g := ![![![-35, -102, -297], ![-10, 483, 0]], ![![17, 31, 89], ![11, -144, 0]]]
    h := ![![![-3302, 82281, -9797], ![1829, 248846, 0]], ![![3702, -90832, 10815], ![-1851, -274703, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {8} * I127N2 =  Ideal.span {B.equivFun.symm ![-309, -16, 11]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E127RS2 


noncomputable def E137RS1 : RelationCertificate Table 16 ![![137, 0, 0], ![-43, 1, 0]]
  ![2303, 480, 135] ![![16, 0, 0], ![1, 1, 0]] where
    su := ![![2192, 0, 0], ![-688, 16, 0]]
    hsu := by decide
    w := ![![36848, 7680, 2160], ![40928, 8528, 2400]]
    hw := by decide
    g := ![![![8808398, 8808529, 22193370], ![1101071, -71018775, 0]], ![![-2727336, -2727383, -6871725], ![-340904, 21989517, 0]]]
    h := ![![![40008, -968995, 115375], ![-19621, -3161248, 0]], ![![44445, -1076288, 128150], ![-21771, -3511280, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {16} * I137N1 =  Ideal.span {B.equivFun.symm ![2303, 480, 135]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E137RS1 
