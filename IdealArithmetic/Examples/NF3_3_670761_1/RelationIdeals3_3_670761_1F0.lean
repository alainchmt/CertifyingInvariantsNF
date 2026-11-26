import IdealArithmetic.Examples.NF3_3_670761_1.PrimesBelow3_3_670761_1F0
import IdealArithmetic.Examples.NF3_3_670761_1.ClassGroupData3_3_670761_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 11 ![![3, 0, 0], ![-1, 1, 0]]
  ![-34, 0, 1] ![![11, 0, 0], ![-19, -6, 1]] where
    su := ![![33, 0, 0], ![-11, 11, 0]]
    hsu := by decide
    w := ![![-374, 0, 11], ![605, 77, -55]]
    hw := by decide
    g := ![![![-4, -133, 344], ![119, 64, 0]], ![![1, 8, -22], ![-7, -4, 0]]]
    h := ![![![-3702, -4288, 7979], ![-192, -2176, 0]], ![![5611, 6495, -12087], ![298, 3296, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {11} * I3N0 =  Ideal.span {B.equivFun.symm ![-34, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS0 


noncomputable def E7RS0 : RelationCertificate Table 3179 ![![7, 0, 0], ![0, 1, 0]]
  ![-202, -77, 37] ![![3179, 0, 0], ![10595, 333, -637]] where
    su := ![![22253, 0, 0], ![0, 3179, 0]]
    hsu := by decide
    w := ![![-642158, -244783, 117623], ![-1525920, 397375, -114444]]
    hw := by decide
    g := ![![![36399512327, 712708753412, -21182165090], ![200213265580, 407686094133, 0]], ![![9044604719, 177095077821, -5263379789], ![49749333630, 101302531112, 0]]]
    h := ![![![404, 413, -947], ![62, 606, 0]], ![![960, 1025, -2268], ![150, 1440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3179} * I7N0 =  Ideal.span {B.equivFun.symm ![-202, -77, 37]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 1 ![![11, 0, 0], ![-15, 2, 1]]
  ![1, 0, 0] ![![11, 0, 0], ![-19, -6, 1]] where
    su := ![![11, 0, 0], ![-15, 2, 1]]
    hsu := by decide
    w := ![![11, 0, 0], ![-19, -6, 1]]
    hw := by decide
    g := ![![![104, 1662, -4261], ![-1441, -792, 0]], ![![-113, -2290, 5895], ![2012, 1096, 0]]]
    h := ![![![16, 36, -402], ![-33, 165, 0]], ![![-2, -62, 649], ![71, -267, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {1} * I11N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 11 ![![11, 0, 0], ![-18, -1, 1]]
  ![12, 0, -1] ![![11, 0, 0], ![-19, -6, 1]] where
    su := ![![121, 0, 0], ![-198, -11, 11]]
    hsu := by decide
    w := ![![132, 0, -11], ![-187, 55, 33]]
    hw := by decide
    g := ![![![1535, 27807, -71437], ![-24274, -13280, 0]], ![![-3634, -66721, 171446], ![58286, 31872, 0]]]
    h := ![![![2508, 9972, -5783], ![-5508, -11520, 0]], ![![-3649, -14644, 8492], ![8111, 16920, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {11} * I11N1 =  Ideal.span {B.equivFun.symm ![12, 0, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 11 ![![11, 0, 0], ![-1, 1, 0]]
  ![23, 0, -1] ![![11, 0, 0], ![-19, -6, 1]] where
    su := ![![121, 0, 0], ![-11, 11, 0]]
    hsu := by decide
    w := ![![253, 0, -11], ![-396, -11, 44]]
    hw := by decide
    g := ![![![5917, 23668, -157140], ![-41949, -27846, -3423]], ![![1609, 6436, -44954], ![-11970, -7956, -1007]]]
    h := ![![![15147, 56406, 9869], ![3754, 0, -27140]], ![![-23642, -88043, -15404], ![-5854, 0, 42362]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {11} * I11N2 =  Ideal.span {B.equivFun.symm ![23, 0, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 2057 ![![13, 0, 0], ![0, 1, 0]]
  ![1288, -33, -23] ![![2057, 0, 0], ![15119, 1423, -830]] where
    su := ![![26741, 0, 0], ![0, 2057, 0]]
    hsu := by decide
    w := ![![2649416, -67881, -47311], ![19580583, 1655885, -1425501]]
    hw := by decide
    g := ![![![-47143, 358842, -393244], ![66509, 75120, 0]], ![![-772786, 5924398, -6492103], ![1097209, 1240106, 0]]]
    h := ![![![-13244504, -13166697, 29138125], ![-1012812, -34435968, 0]], ![![-97883877, -97308756, 215346087], ![-7485287, -254499984, 0]]]
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
  ![763, -858, -785] ![![34969, 0, 0], ![-62729, -17127, 3374]] where
    su := ![![1084039, 0, 0], ![279752, 34969, 0]]
    hsu := by decide
    w := ![![26681347, -30003402, -27450665], ![-44795289, 180789730, 192049748]]
    hw := by decide
    g := ![![![186440349012923, 4229561355670517, -9688219697255402], ![-3340758021299104, -2040839472253274, 0]], ![![52079638489041471716990, 1181471862631064877816901, -2706275665200298142535327], ![-933196440517233451606733, -570081436314366667708518, 0]]]
    h := ![![![-644195433, 415115575, 1504011115], ![-152853133, -4238576850, 0]], ![![1695996879, -1092889865, -3959664958], ![402422115, 11159056290, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {34969} * I31N0 =  Ideal.span {B.equivFun.symm ![763, -858, -785]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 34969 ![![31, 0, 0], ![11, 1, 0]]
  ![12059, 143, -399] ![![34969, 0, 0], ![-62729, -17127, 3374]] where
    su := ![![1084039, 0, 0], ![384659, 34969, 0]]
    hsu := by decide
    w := ![![421691171, 5000567, -13952631], ![-693575146, -49795856, 37661613]]
    hw := by decide
    g := ![![![432587290669162, 9813618659175628, -22479043475253151], ![-7751377151655182, -4735247615802830, 0]], ![![169104350923421, 3836279171817252, -8787368786297498], ![-3030120463432927, -1851073740761862, 0]]]
    h := ![![![32252962893, -43306018423, -78800152369], ![10047631416, 222073156640, 0]], ![![-52860789348, 70976124678, 129149010843], ![-16467501866, -363965394096, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {34969} * I31N1 =  Ideal.span {B.equivFun.symm ![12059, 143, -399]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 34969 ![![31, 0, 0], ![12, 1, 0]]
  ![507, 209, 395] ![![34969, 0, 0], ![-62729, -17127, 3374]] where
    su := ![![1084039, 0, 0], ![419628, 34969, 0]]
    hsu := by decide
    w := ![![17729283, 7308521, 13812755], ![-56929532, -128615982, -55425865]]
    hw := by decide
    g := ![![![-48229710, -1095013466, 2508256797], ![864936854, 528368880, 0]], ![![-22904774, -520025383, 1191178951], ![410761008, 250924020, 0]]]
    h := ![![![2739, -4347, -6781], ![944, 19146, 0]], ![![-7538, 11808, 18563], ![-2520, -52458, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {34969} * I31N2 =  Ideal.span {B.equivFun.symm ![507, 209, 395]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS2 
