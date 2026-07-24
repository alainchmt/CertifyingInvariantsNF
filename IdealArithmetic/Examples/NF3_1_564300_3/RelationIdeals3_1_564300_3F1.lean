import IdealArithmetic.Examples.NF3_1_564300_3.PrimesBelow3_1_564300_3F1
import IdealArithmetic.Examples.NF3_1_564300_3.ClassGroupData3_1_564300_3

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 4941258 ![![37, 0, 0], ![4, 1, 0]]
  ![284682, 6036, 10217] ![![4941258, 0, 0], ![-1563582, 1, 0]] where
    su := ![![182826546, 0, 0], ![19765032, 4941258, 0]]
    hsu := by decide
    w := ![![1406687209956, 29825433288, 50484832986], ![-445123344414, -9437802780, -15975087114]]
    hw := by decide
    g := ![![![983870201870254174219454225, 16901933957085514302302861242570935, -54048760976674531759431604456], ![3109243075165234954351784521, 53413774513216168690509098194209146, 0]], ![![99716574513876092009992798, 1713033847001892706559193120939931, -5477914963852092442239531462], ![315125987347824642809339704, 5413558227690772519391124550571835, 0]]]
    h := ![![![4718063675498, 1195478324378, 19953009356], ![-43642088927186, -147652267191, 0]], ![![-1492954701275, -378289719555, -6313806079], ![13809830964273, 46722164338, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {4941258} * I37N1 =  Ideal.span {B.equivFun.symm ![284682, 6036, 10217]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 6 ![![41, 0, 0], ![5, 1, 0]]
  ![36, 0, 1] ![![6, 0, 0], ![0, 1, 0]] where
    su := ![![246, 0, 0], ![30, 6, 0]]
    hsu := by decide
    w := ![![216, 0, 6], ![30, 6, 0]]
    hw := by decide
    g := ![![![1, 239, -1], ![-1433, 1, 0]], ![![0, 29, 0], ![-173, 0, 0]]]
    h := ![![![836, 168, 1], ![-6848, -8, 0]], ![![115, 23, 0], ![-942, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {6} * I41N1 =  Ideal.span {B.equivFun.symm ![36, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 5764801 ![![43, 0, 0], ![1, 1, 0]]
  ![35467, -3622, -5858] ![![5764801, 0, 0], ![-740039, 1, 0]] where
    su := ![![247886443, 0, 0], ![5764801, 5764801, 0]]
    hsu := by decide
    w := ![![204460197067, -20880109222, -33770204258], ![-26247138953, 2680632465, 4335130352]]
    hw := by decide
    g := ![![![1794, -14629296090805, 98841386], ![13975, -113960184170792, 0]], ![![524020, -527550417868, 3564342], ![4082043, -4109544465186, 0]]]
    h := ![![![1646, 737, -136], ![-35311, -2, 0]], ![![-212, -96, 14], ![4563, 30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {5764801} * I43N1 =  Ideal.span {B.equivFun.symm ![35467, -3622, -5858]} * (J0 ^ 8*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_0 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 343 ![![47, 0, 0], ![-10, 1, 0]]
  ![-13, 33, 10] ![![343, 0, 0], ![155, 1, 0]] where
    su := ![![16121, 0, 0], ![-3430, 343, 0]]
    hsu := by decide
    w := ![![-4459, 11319, 3430], ![-1715, 4802, 1715]]
    hw := by decide
    g := ![![![351, -370295, -11945], ![-772, 819432, 0]], ![![-225, 69594, 2245], ![497, -154008, 0]]]
    h := ![![![-50929, 5294, -100], ![-239365, 942, 0]], ![![-19625, 2043, -40], ![-92237, 377, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {343} * I47N1 =  Ideal.span {B.equivFun.symm ![-13, 33, 10]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E47RS1 


noncomputable def E53RS0 : RelationCertificate Table 343 ![![53, 0, 0], ![10, 1, 0]]
  ![-53, 29, -12] ![![343, 0, 0], ![155, 1, 0]] where
    su := ![![18179, 0, 0], ![3430, 343, 0]]
    hsu := by decide
    w := ![![-18179, 9947, -4116], ![-8575, 4802, -1715]]
    hw := by decide
    g := ![![![52748504, -48213537651, -1555286386], ![-116727339, 106692646075, 0]], ![![10823425, -9892918631, -319128660], ![-23951193, 21892226075, 0]]]
    h := ![![![-161, -23, -4], ![848, 40, 0]], ![![-85, -18, -5], ![448, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {343} * I53N0 =  Ideal.span {B.equivFun.symm ![-53, 29, -12]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 49 ![![53, 0, 0], ![21, 1, 0]]
  ![17, -13, 2] ![![49, 0, 0], ![8, 1, 0]] where
    su := ![![2597, 0, 0], ![1029, 49, 0]]
    hsu := by decide
    w := ![![833, -637, 98], ![196, -147, -49]]
    hw := by decide
    g := ![![![-5, 4207, 2631], ![102, -25780, 0]], ![![-3, 1746, 1092], ![48, -10700, 0]]]
    h := ![![![6439, 407, 24], ![-16250, -254, 0]], ![![1520, 85, 3], ![-3836, -32, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {49} * I53N1 =  Ideal.span {B.equivFun.symm ![17, -13, 2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 2401 ![![53, 0, 0], ![22, 1, 0]]
  ![-257, -60, 13] ![![2401, 0, 0], ![-531, 1, 0]] where
    su := ![![127253, 0, 0], ![52822, 2401, 0]]
    hsu := by decide
    w := ![![-617057, -144060, 31213], ![136857, 31213, -7203]]
    hw := by decide
    g := ![![![-229394806, -2612235876360, 24597328704], ![-1037244687, -11811637243663, 0]], ![![-108024716, -1230134098894, 11583185521], ![-488450740, -5562245687185, 0]]]
    h := ![![![-6182383, -371039, -20459], ![14893911, 216868, 0]], ![![1370951, 82266, 4534], ![-3302743, -48061, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {2401} * I53N2 =  Ideal.span {B.equivFun.symm ![-257, -60, 13]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E53RS2 


noncomputable def E61RS1 : RelationCertificate Table 14406 ![![61, 0, 0], ![-21, 1, 0]]
  ![-1116, 300, -65] ![![14406, 0, 0], ![6672, 1, 0]] where
    su := ![![878766, 0, 0], ![-302526, 14406, 0]]
    hsu := by decide
    w := ![![-16077096, 4321800, -936390], ![-7447902, 2002434, -432180]]
    hw := by decide
    g := ![![![4155053, -157001960542, -117657345], ![-8971477, 338994342407, 0]], ![![-1448320, 54564936838, 40890990], ![3127173, -117815120386, 0]]]
    h := ![![![-437299956, 22517100, -403165], ![-1270252200, 4918600, 0]], ![![-202584358, 10431308, -186770], ![-588459301, 2278588, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {14406} * I61N1 =  Ideal.span {B.equivFun.symm ![-1116, 300, -65]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 294 ![![67, 0, 0], ![-21, 1, 0]]
  ![-48, 5, 3] ![![294, 0, 0], ![144, 0, 1]] where
    su := ![![19698, 0, 0], ![-6174, 294, 0]]
    hsu := by decide
    w := ![![-14112, 1470, 882], ![-6762, 588, 294]]
    hw := by decide
    g := ![![![-68631028, -323362033, 114335], ![-33614501, 833933664, 0]], ![![19461256, 91694095, -32422], ![9532071, -236474245, 0]]]
    h := ![![![-306, 19, -1], ![-974, 14, 0]], ![![-137, 15, -2], ![-436, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {294} * I67N1 =  Ideal.span {B.equivFun.symm ![-48, 5, 3]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E67RS1 


noncomputable def E71RS0 : RelationCertificate Table 7 ![![71, 0, 0], ![25, 1, 0]]
  ![59, 1, 2] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![497, 0, 0], ![175, 7, 0]]
    hsu := by decide
    w := ![![413, 7, 14], ![119, 0, 7]]
    hw := by decide
    g := ![![![-1138, 56975, 290578], ![7979, -406809, 0]], ![![-409, 20452, 104310], ![2868, -146034, 0]]]
    h := ![![![5179, 242, 7], ![-14706, -99, 0]], ![![1477, 64, 1], ![-4194, -14, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {7} * I71N0 =  Ideal.span {B.equivFun.symm ![59, 1, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 14406 ![![71, 0, 0], ![-17, 1, 0]]
  ![114, -263, 97] ![![14406, 0, 0], ![-3090, 0, 1]] where
    su := ![![1022826, 0, 0], ![-244902, 14406, 0]]
    hsu := by decide
    w := ![![1642284, -3788778, 1397382], ![-360150, 821142, -302526]]
    hw := by decide
    g := ![![![-565913754475591, 61562812638962474, -8426008755], ![121385082124273, 284254448357978654, 0]], ![![137094294798582, -14913774966071199, 2041225750], ![-29405898154441, -68861487872186440, 0]]]
    h := ![![![32780356, -2016883, 26067], ![136906186, -370132, 0]], ![![-7187580, 442250, -5721], ![-30018715, 81234, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {14406} * I71N1 =  Ideal.span {B.equivFun.symm ![114, -263, 97]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 14406 ![![71, 0, 0], ![-8, 1, 0]]
  ![5736, 162, 205] ![![14406, 0, 0], ![6672, 1, 0]] where
    su := ![![1022826, 0, 0], ![-115248, 14406, 0]]
    hsu := by decide
    w := ![![82632816, 2333772, 2953230], ![38276742, 1080450, 1368570]]
    hw := by decide
    g := ![![![-16207426466404484900, 612268620072456839904057, 458834399356735216845], ![34994632145537021803, -1321993671426625506773811, 0]], ![![1902280101549793949, -71862514087689794782933, -53853802737412858870], ![-4107351190486560496, 155163576447033928976243, 0]]]
    h := ![![![7032, -870, 5], ![61692, -30, 0]], ![![3263, -400, 0], ![28627, 19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {14406} * I71N2 =  Ideal.span {B.equivFun.symm ![5736, 162, 205]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E71RS2 


noncomputable def E73RS1 : RelationCertificate Table 705894 ![![73, 0, 0], ![-15, 1, 0]]
  ![-22122, -2418, -1637] ![![705894, 0, 0], ![-151794, 1, 0]] where
    su := ![![51530262, 0, 0], ![-10588410, 705894, 0]]
    hsu := by decide
    w := ![![-15615787068, -1706851692, -1155548478], ![3357937758, 367064880, 248474688]]
    hw := by decide
    g := ![![![-1454888922415294369379598, -4996732279171757724005537904519, 164589255147810267577945199], ![-6765730931390053648884949, -23236513534661676204333209660602, 0]], ![![308914771197647485798760, 1060950004481260745621819352100, -34947033627261151222321410], ![1436559307349382547007325, 4933780271056376616185869878113, 0]]]
    h := ![![![-277108533234, 19103683452, -209927119], ![-1348594860264, 3064935610, 0]], ![![59587977359, -4107956700, 45141634], ![289994822830, -659067786, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {705894} * I73N1 =  Ideal.span {B.equivFun.symm ![-22122, -2418, -1637]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E73RS1 


noncomputable def E79RS0 : RelationCertificate Table 2401 ![![79, 0, 0], ![21, 1, 0]]
  ![1399, 37, 32] ![![2401, 0, 0], ![-531, 1, 0]] where
    su := ![![189679, 0, 0], ![50421, 2401, 0]]
    hsu := by decide
    w := ![![3358999, 88837, 76832], ![-741909, -19208, -16807]]
    hw := by decide
    g := ![![![775, 4511693, -42483], ![3504, 20400336, 0]], ![![165, 1402052, -13202], ![746, 6339600, 0]]]
    h := ![![![42175549, 2229185, 52578], ![-158660332, -830726, 0]], ![![-9315387, -492385, -11618], ![35043584, 183563, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {2401} * I79N0 =  Ideal.span {B.equivFun.symm ![1399, 37, 32]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 294 ![![79, 0, 0], ![-19, 1, 0]]
  ![-114, 18, 1] ![![294, 0, 0], ![-90, 1, 0]] where
    su := ![![23226, 0, 0], ![-5586, 294, 0]]
    hsu := by decide
    w := ![![-33516, 5292, 294], ![10290, -1764, 0]]
    hw := by decide
    g := ![![![54, -6319, 351], ![179, -20640, 0]], ![![6, -2322, 129], ![19, -7585, 0]]]
    h := ![![![-874, 50, -1], ![-3628, 16, 0]], ![![284, -15, 0], ![1179, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {294} * I79N1 =  Ideal.span {B.equivFun.symm ![-114, 18, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 2058 ![![79, 0, 0], ![-2, 1, 0]]
  ![-396, 29, -12] ![![2058, 0, 0], ![1026, 0, 1]] where
    su := ![![162582, 0, 0], ![-4116, 2058, 0]]
    hsu := by decide
    w := ![![-814968, 59682, -24696], ![-405426, 28812, -12348]]
    hw := by decide
    g := ![![![-16702938314, -692364685178, 4046218], ![-8327116655, 1430608957928, 0]], ![![223322087, 9257078312, -54099], ![111335740, -19127577476, 0]]]
    h := ![![![-1670324, 835681, -1303], ![-65977600, 20585, 0]], ![![-830941, 415729, -649], ![-32822071, 10253, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {2058} * I79N2 =  Ideal.span {B.equivFun.symm ![-396, 29, -12]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E79RS2 
