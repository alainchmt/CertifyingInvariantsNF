import IdealArithmetic.Examples.NF3_3_670761_1.PrimesBelow3_3_670761_1F0
import IdealArithmetic.Examples.NF3_3_670761_1.ClassGroupData3_3_670761_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 11 ![![3, 0, 0], ![-1, 1, 0]]
  ![-34, 0, 1] ![![11, 0, 0], ![-16, 0, 1]] where
    su := ![![33, 0, 0], ![-11, 11, 0]]
    hsu := by decide
    w := ![![-374, 0, 11], ![539, 11, -22]]
    hw := by decide
    g := ![![![-2243, -7331, -5489], ![2778, 11520, 0]], ![![432, 1374, 1028], ![-513, -2160, 0]]]
    h := ![![![-3702, -4288, 7979], ![-192, -2176, 0]], ![![5283, 6115, -11382], ![280, 3104, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {11} * I3N0 =  Ideal.span {B.equivFun.symm ![-34, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS0 


noncomputable def E7RS0 : RelationCertificate Table 3179 ![![7, 0, 0], ![0, 1, 0]]
  ![-202, -77, 37] ![![3179, 0, 0], ![-25814, 63, 1505]] where
    su := ![![22253, 0, 0], ![0, 3179, 0]]
    hsu := by decide
    w := ![![-642158, -244783, 117623], ![4278934, 0, -321079]]
    hw := by decide
    g := ![![![-220470, -2979891, -3044240], ![348852, 1113728, 0]], ![![-776511963245, -10167181597266, -10385380941990], ![1187275778117, 3799984907340, 0]]]
    h := ![![![404, 413, -947], ![62, 606, 0]], ![![-2692, -2827, 6331], ![-401, -4038, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3179} * I7N0 =  Ideal.span {B.equivFun.symm ![-202, -77, 37]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 1 ![![11, 0, 0], ![-80, 0, 5]]
  ![1, 0, 0] ![![11, 0, 0], ![-16, 0, 1]] where
    su := ![![11, 0, 0], ![-80, 0, 5]]
    hsu := by decide
    w := ![![11, 0, 0], ![-16, 0, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![5, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![64, 0, -4], ![9, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {1} * I11N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 11 ![![11, 0, 0], ![-18, -1, 1]]
  ![12, 0, -1] ![![11, 0, 0], ![-16, 0, 1]] where
    su := ![![121, 0, 0], ![-198, -11, 11]]
    hsu := by decide
    w := ![![132, 0, -11], ![-187, -11, 0]]
    hw := by decide
    g := ![![![5, -19, -15], ![14, 30, 0]], ![![26, 44, 32], ![-7, -69, 0]]]
    h := ![![![2508, 9972, -5783], ![-5508, -11520, 0]], ![![-3505, -14022, 8131], ![7759, 16200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {11} * I11N1 =  Ideal.span {B.equivFun.symm ![12, 0, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 11 ![![11, 0, 0], ![-1, 1, 0]]
  ![23, 0, -1] ![![11, 0, 0], ![-16, 0, 1]] where
    su := ![![121, 0, 0], ![-11, 11, 0]]
    hsu := by decide
    w := ![![253, 0, -11], ![-363, -11, 11]]
    hw := by decide
    g := ![![![-2278, -9112, -4310], ![11590, 27888, -8635]], ![![-95, -380, -149], ![578, 1328, -465]]]
    h := ![![![15147, 56406, 9869], ![3754, 0, -27140]], ![![-21666, -80686, -14117], ![-5361, 0, 38822]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {11} * I11N2 =  Ideal.span {B.equivFun.symm ![23, 0, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 2057 ![![13, 0, 0], ![0, 1, 0]]
  ![1288, -33, -23] ![![2057, 0, 0], ![-2092, 70, 124]] where
    su := ![![26741, 0, 0], ![0, 2057, 0]]
    hsu := by decide
    w := ![![2649416, -67881, -47311], ![-2702898, 8228, 74052]]
    hw := by decide
    g := ![![![-897216, -1534357, -5171550], ![549923, 7604092, 0]], ![![-80217, -140649, -473951], ![52341, 696710, 0]]]
    h := ![![![-13244504, -13166697, 29138125], ![-1012812, -34435968, 0]], ![![13511862, 13432481, -29726316], ![1033271, 35131104, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {2057} * I13N0 =  Ideal.span {B.equivFun.symm ![1288, -33, -23]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E17RS0 : RelationCertificate Table 17 ![![17, 0, 0], ![8, 1, 0]]
  ![5, 3, -1] ![![17, 0, 0], ![-6, 1, 0]] where
    su := ![![289, 0, 0], ![136, 17, 0]]
    hsu := by decide
    w := ![![85, 51, -17], ![-51, -51, 34]]
    hw := by decide
    g := ![![![-194826, -463303, 460861], ![41513, -712240, 0]], ![![-95396, -226859, 225663], ![20332, -348752, 0]]]
    h := ![![![85, -66, -233], ![45, 360, 0]], ![![-53, 38, 136], ![-19, -210, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {17} * I17N0 =  Ideal.span {B.equivFun.symm ![5, 3, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 1 ![![17, 0, 0], ![-6, 1, 0]]
  ![1, 0, 0] ![![17, 0, 0], ![-6, 1, 0]] where
    su := ![![17, 0, 0], ![-6, 1, 0]]
    hsu := by decide
    w := ![![17, 0, 0], ![-6, 1, 0]]
    hw := by decide
    g := ![![![135, 309, -308], ![-17, 476, 0]], ![![-44, -111, 110], ![18, -170, 0]]]
    h := ![![![135, 309, -308], ![-17, 476, 0]], ![![-44, -111, 110], ![18, -170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {1} * I17N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 17 ![![17, 0, 0], ![-2, 1, 0]]
  ![12, -3, 1] ![![17, 0, 0], ![-6, 1, 0]] where
    su := ![![289, 0, 0], ![-34, 17, 0]]
    hsu := by decide
    w := ![![204, -51, 17], ![-51, 68, -34]]
    hw := by decide
    g := ![![![22, 48, -48], ![-3, 74, 0]], ![![11, 12, -13], ![15, 20, 0]]]
    h := ![![![31, 40, -64], ![10, 99, 0]], ![![-7, -12, 18], ![12, -28, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {17} * I17N2 =  Ideal.span {B.equivFun.symm ![12, -3, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS2 


noncomputable def E31RS0 : RelationCertificate Table 34969 ![![31, 0, 0], ![8, 1, 0]]
  ![763, -858, -785] ![![34969, 0, 0], ![171278, 17456, -9278]] where
    su := ![![1084039, 0, 0], ![279752, 34969, 0]]
    hsu := by decide
    w := ![![26681347, -30003402, -27450665], ![134700588, -110711854, -131063812]]
    hw := by decide
    g := ![![![-88827903, 804268869, -971811068], ![224852978, 247685490, 0]], ![![-85075219, 770350416, -930826407], ![215368742, 237239640, 0]]]
    h := ![![![-644195433, 415115575, 1504011115], ![-152853133, -4238576850, 0]], ![![-3060175410, 1971958265, 7144629782], ![-726111111, -20134866090, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {34969} * I31N0 =  Ideal.span {B.equivFun.symm ![763, -858, -785]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 34969 ![![31, 0, 0], ![11, 1, 0]]
  ![12059, 143, -399] ![![34969, 0, 0], ![171278, 17456, -9278]] where
    su := ![![1084039, 0, 0], ![384659, 34969, 0]]
    hsu := by decide
    w := ![![421691171, 5000567, -13952631], ![1984700564, 72525706, -90569710]]
    hw := by decide
    g := ![![![-265372658670124, 2405985993602238, -2907167344926019], ![672569759466411, 740944866390942, 0]], ![![-494454458874852, 4482943001192033, -5416766987364162], ![1253162696685107, 1380562319098113, 0]]]
    h := ![![![32252962893, -43306018423, -78800152369], ![10047631416, 222073156640, 0]], ![![151578849520, -203524757374, -370336098322], ![47220728636, 1043674458672, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {34969} * I31N1 =  Ideal.span {B.equivFun.symm ![12059, 143, -399]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 34969 ![![31, 0, 0], ![12, 1, 0]]
  ![507, 209, 395] ![![34969, 0, 0], ![171278, 17456, -9278]] where
    su := ![![1084039, 0, 0], ![419628, 34969, 0]]
    hsu := by decide
    w := ![![17729283, 7308521, 13812755], ![116656584, 100081278, 25247618]]
    hw := by decide
    g := ![![![-856427750, 7763847900, -9381110917], ![2170330415, 2390949372, 0]], ![![-334122066, 3027913225, -3658656181], ![846458564, 932477652, 0]]]
    h := ![![![2739, -4347, -6781], ![944, 19146, 0]], ![![17430, -27537, -43096], ![5883, 121518, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {34969} * I31N2 =  Ideal.span {B.equivFun.symm ![507, 209, 395]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS2 
