import IdealArithmetic.Examples.NF3_1_547575_2.PrimesBelow3_1_547575_2F0
import IdealArithmetic.Examples.NF3_1_547575_2.ClassGroupData3_1_547575_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 4 ![![2, 0, 0], ![27, 1, 1]]
  ![695, 5, 17] ![![4, 0, 0], ![28, -1, 1]] where
    su := ![![8, 0, 0], ![108, 4, 4]]
    hsu := by decide
    w := ![![2780, 20, 68], ![18968, 136, 464]]
    hw := by decide
    g := ![![![-20, -1, -1], ![3, 0, 0]], ![![-23, 16, 0], ![2, 0, 0]]]
    h := ![![![1432, -33499, 2732], ![4213, -4830, 0]], ![![9880, -228566, 18645], ![28738, -32956, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {4} * I2N0 =  Ideal.span {B.equivFun.symm ![695, 5, 17]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![28, 0, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![28, 0, 1]] where
    su := ![![2, 0, 0], ![28, 0, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![28, 0, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E2RS2 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![27, -39, 1], ![-4, 0, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![27, -39, 1], ![-4, 0, -2]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N2 : Ideal.span {1} * I2N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS2 


noncomputable def E3RS0 : RelationCertificate Table 2 ![![3, 0, 0], ![0, 1, 0]]
  ![55584384633, 399151635, 1359736433] ![![2, 0, 0], ![28, 1, 1]] where
    su := ![![6, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![111168769266, 798303270, 2719472866], ![1582259246160, 11362208456, 38706114274]]
    hw := by decide
    g := ![![![1299, -32153, -1882], ![1219, 0, 0]], ![![180, 13368, -20659], ![-740, 0, 0]]]
    h := ![![![18528128211, -1919859159, -4079209299], ![-639953053, 6798682165, 0]], ![![263709874360, -27325254438, -58059171411], ![-9108418143, 96765285685, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {2} * I3N0 =  Ideal.span {B.equivFun.symm ![55584384633, 399151635, 1359736433]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 2 ![![3, 0, 0], ![1, 1, 0]]
  ![35940588925, -60420554689, 3857807149] ![![2, 0, 0], ![28, 1, 1]] where
    su := ![![6, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![71881177850, -120841109378, 7715614298], ![-397463136848, 649110837872, -135052013390]]
    hw := by decide
    g := ![![![1059280621626730099639, -4631243184867801170709, -1803356619840764301318], ![11612628800419938659155, 0, 0]], ![![560395280195452807025, -2450084301789309427995, -954036652455729474965], ![6143473445613819847261, 0, 0]]]
    h := ![![![-32956666194, -57821883756, 8541099359], ![134810587507, -10882745464, 0]], ![![177030228510, 315713265028, -58254628167], ![-729822253954, 53618938903, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {2} * I3N1 =  Ideal.span {B.equivFun.symm ![35940588925, -60420554689, 3857807149]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 2 ![![5, 0, 0], ![-2, 1, 0]]
  ![3672002, -5437281, 3958250] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![10, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![7344004, -10874562, 7916500], ![98670002, -169490810, -6916312]]
    hw := by decide
    g := ![![![6025154241681995, -1163435123646333, 177123232627581], ![2430859559017831, 0, -76]], ![![-1702586304139714, 328763153243398, -50051430705361], ![-686911575448158, 0, 0]]]
    h := ![![![734402, 1468800, -4320864], ![4, 12781285, 0]], ![![9867001, 19734000, -74057794], ![2, 183415407, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2} * I5N0 =  Ideal.span {B.equivFun.symm ![3672002, -5437281, 3958250]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![2, 1, 0]]
  ![-2, 3, -2] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![14, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![-4, 6, -4], ![-50, 86, 4]]
    hw := by decide
    g := ![![![840, 728, 19], ![785, 0, 54]], ![![-147, 918, -10], ![388, 0, 54]]]
    h := ![![![-6, -5, -2], ![20, 6, 0]], ![![-29, -16, -6], ![89, 22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-2, 3, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 4 ![![11, 0, 0], ![1, 1, 0]]
  ![-959749, 1580612, -262109] ![![4, 0, 0], ![28, 0, 1]] where
    su := ![![44, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![-3838996, 6322448, -1048436], ![14207024, -23693264, 2447668]]
    hw := by decide
    g := ![![![415075566561, 146337770060, -214468661857], ![2851911800497, 0, 0]], ![![59887913195, 21113899249, -30943957297], ![411479403147, 15, 0]]]
    h := ![![![117484, 342003, -30251], ![-2252073, 35326, 0]], ![![-443192, -1279578, 80613], ![8426868, -137413, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {4} * I11N0 =  Ideal.span {B.equivFun.symm ![-959749, 1580612, -262109]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 4 ![![11, 0, 0], ![3, 1, 0]]
  ![129901073, 932820, 3177713] ![![4, 0, 0], ![28, 0, 1]] where
    su := ![![44, 0, 0], ![12, 4, 0]]
    hsu := by decide
    w := ![![519604292, 3731280, 12710852], ![3621485168, 26005896, 88590804]]
    hw := by decide
    g := ![![![167, -4554, -118], ![1277, -1566, 0]], ![![67297094195, -1717560397410, -110842272661], ![443369091253, -528480122101, 0]]]
    h := ![![![125977351, 43475040, 2955975], ![-418616596, -14669006, 0]], ![![878024140, 303007926, 20602259], ![-2917631416, -102238574, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {4} * I11N1 =  Ideal.span {B.equivFun.symm ![129901073, 932820, 3177713]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 4 ![![11, 0, 0], ![-5, 1, 0]]
  ![28217, -47148, 4425] ![![4, 0, 0], ![28, 0, 1]] where
    su := ![![44, 0, 0], ![-20, 4, 0]]
    hsu := by decide
    w := ![![112868, -188592, 17700], ![-394576, 666024, -29308]]
    hw := by decide
    g := ![![![277498199, 97833348, -143382764], ![1906641833, -174, 0]], ![![-63977025, -1247657906, -20463152], ![-452954899, -371818345, 0]]]
    h := ![![![5827, 108060, -56097], ![7176, 310746, 0]], ![![-20424, -379438, 197767], ![-25204, -1091382, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {4} * I11N2 =  Ideal.span {B.equivFun.symm ![28217, -47148, 4425]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 4 ![![13, 0, 0], ![30, 3, 1]]
  ![185792207718833, 1334174408350, 4544953325845] ![![4, 0, 0], ![28, 1, 1]] where
    su := ![![52, 0, 0], ![120, 12, 4]]
    hsu := by decide
    w := ![![743168830875332, 5336697633400, 18179813303380], ![5288741441837864, 37978468369128, 129376163299548]]
    hw := by decide
    g := ![![![-9241, 116756, 117358], ![-6093, -412, 0]], ![![53264, -1094846, -68358], ![82219, -927, 0]]]
    h := ![![![2352632842721, -1091278743692, -48357387149], ![5173599358782, 0, 0]], ![![16742449758242, -7766056482150, -344134073989], ![36817783786744, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {4} * I13N0 =  Ideal.span {B.equivFun.symm ![185792207718833, 1334174408350, 4544953325845]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 4 ![![13, 0, 0], ![-6, 1, 0]]
  ![46910, -76085, 18484] ![![4, 0, 0], ![26, 1, 1]] where
    su := ![![52, 0, 0], ![-24, 4, 0]]
    hsu := by decide
    w := ![![187640, -304340, 73936], ![-384572, 576064, -382520]]
    hw := by decide
    g := ![![![3304158178, -4048719723, -1741713483], ![20029420025, 0, 618]], ![![-1375774898, 1685793376, 725209299], ![-8339786018, 0, -206]]]
    h := ![![![1263470, -237795, 10208], ![2729700, -57110, 0]], ![![-2576975, 484261, -25324], ![-5567422, 116791, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {4} * I13N1 =  Ideal.span {B.equivFun.symm ![46910, -76085, 18484]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![-1, 1, 0]]
  ![9524, -18211, -9634] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![68, 0, 0], ![-4, 4, 0]]
    hsu := by decide
    w := ![![38096, -72844, -38536], ![-221692, 368096, -46056]]
    hw := by decide
    g := ![![![10576376753, -546421638, 274060160], ![2507488781, 15, 0]], ![![-256880608, 13271569, -6656414], ![-60902257, 0, 0]]]
    h := ![![![1110, -1621, -560], ![9346, -57, 0]], ![![-6460, 8613, -670], ![-54397, -62, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![9524, -18211, -9634]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![4, 1, 0]]
  ![13, -24, -9] ![![2, 0, 0], ![28, 0, 1]] where
    su := ![![38, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![26, -48, -18], ![-104, 204, 130]]
    hw := by decide
    g := ![![![223, 321, -495], ![3177, 0, 0]], ![![32, 97, -119], ![766, 3, 0]]]
    h := ![![![11, 0, -1], ![-49, 5, 0]], ![![-52, -13, 1], ![234, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![13, -24, -9]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![5, 1, 0]]
  ![-33932698, 43637053, -68587974] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![38, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![-67865396, 87274106, -137175948], ![-1680044074, 2865448342, 18686132]]
    hw := by decide
    g := ![![![-1678306699718600911, 324074850929718680, -49337676027972926], ![-677115924394441113, 0, 1800]], ![![-493519465428757703, 95296793617374876, -14508136982891757], ![-199111335905691411, 0, 600]]]
    h := ![![![13893878, 4693153, -3856392], ![-59583276, 2341737, 0]], ![![444134447, 150414865, -7061892], ![-1855715306, 71759507, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![-33932698, 43637053, -68587974]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 4 ![![19, 0, 0], ![9, 1, 0]]
  ![2097491, -3490695, 396833] ![![4, 0, 0], ![28, -1, 1]] where
    su := ![![76, 0, 0], ![36, 4, 0]]
    hsu := by decide
    w := ![![8389964, -13962780, 1587332], ![-39332920, 67804388, 3920052]]
    hw := by decide
    g := ![![![-7003979488769, -13505821158851, 3358140004015], ![-44811866130491, 0, 0]], ![![-3534098005855, -6814825157818, 1694464684055], ![-22611363580415, 0, 0]]]
    h := ![![![-743251, 40929895, 8262579], ![1802140, -78296084, 0]], ![![3496337, -192468174, -38709685], ![-8473737, 368232014, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {4} * I19N2 =  Ideal.span {B.equivFun.symm ![2097491, -3490695, 396833]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E19RS2 


noncomputable def E29RS1 : RelationCertificate Table 4 ![![29, 0, 0], ![13, 1, 0]]
  ![223, -366, 67] ![![4, 0, 0], ![28, 1, 1]] where
    su := ![![116, 0, 0], ![52, 4, 0]]
    hsu := by decide
    w := ![![892, -1464, 268], ![-1736, 2672, -1380]]
    hw := by decide
    g := ![![![50321, -65496, -24739], ![329727, 0, 0]], ![![23569, -30709, -11589], ![154491, -7, 0]]]
    h := ![![![-2478, -199, 3], ![5545, -10, 0]], ![![4700, 350, -17], ![-10518, 74, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {4} * I29N1 =  Ideal.span {B.equivFun.symm ![223, -366, 67]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E29RS1 
