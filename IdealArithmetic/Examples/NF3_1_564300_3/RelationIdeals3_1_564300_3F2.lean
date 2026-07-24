import IdealArithmetic.Examples.NF3_1_564300_3.PrimesBelow3_1_564300_3F2
import IdealArithmetic.Examples.NF3_1_564300_3.ClassGroupData3_1_564300_3

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 16807 ![![97, 0, 0], ![38, 1, 0]]
  ![-13987, -61, -507] ![![16807, 0, 0], ![-531, 1, 0]] where
    su := ![![1630279, 0, 0], ![638666, 16807, 0]]
    hsu := by decide
    w := ![![-235079509, -1025227, -8521149], ![7411887, 33614, 268912]]
    hw := by decide
    g := ![![![296, -51669062, 486526], ![9369, -1635408504, 0]], ![![49, -21466100, 202129], ![1551, -679436424, 0]]]
    h := ![![![-105841, -3244, -66], ![269805, 1179, 0]], ![![3327, 71, -2], ![-8481, 42, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {16807} * I97N1 =  Ideal.span {B.equivFun.symm ![-13987, -61, -507]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E97RS1 


noncomputable def E101RS0 : RelationCertificate Table 823543 ![![101, 0, 0], ![11, 1, 0]]
  ![-194009, -1805, -7012] ![![823543, 0, 0], ![83504, 1, 0]] where
    su := ![![83177843, 0, 0], ![9058973, 823543, 0]]
    hsu := by decide
    w := ![![-159774753887, -1486495115, -5774683516], ![-16200737896, -150708369, -585539073]]
    hw := by decide
    g := ![![![14657, -701023144435, -41975423], ![-144552, 6913713156706, 0]], ![![9689, -82204978374, -4922218], ![-95556, 810731635672, 0]]]
    h := ![![![-878593, -80755, -542], ![8049444, 9546, 0]], ![![-89102, -8192, -56], ![816330, 989, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {823543} * I101N0 =  Ideal.span {B.equivFun.symm ![-194009, -1805, -7012]} * (J0 ^ 7*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_0 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 6 ![![101, 0, 0], ![24, 1, 0]]
  ![6, 0, 1] ![![6, 0, 0], ![0, 1, 0]] where
    su := ![![606, 0, 0], ![144, 6, 0]]
    hsu := by decide
    w := ![![36, 0, 6], ![30, -24, 0]]
    hw := by decide
    g := ![![![16, 589, -1], ![-3533, 2, 0]], ![![4, 140, -4], ![-840, 5, 0]]]
    h := ![![![510, 2, -4], ![-2146, 81, 0]], ![![409, 17, 0], ![-1721, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {6} * I101N1 =  Ideal.span {B.equivFun.symm ![6, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 294 ![![101, 0, 0], ![-35, 1, 0]]
  ![66, -13, 2] ![![294, 0, 0], ![144, 0, 1]] where
    su := ![![29694, 0, 0], ![-10290, 294, 0]]
    hsu := by decide
    w := ![![19404, -3822, 588], ![9114, -1470, 294]]
    hw := by decide
    g := ![![![357193472, 1682956428, -595068], ![174950009, -4340256051, 0]], ![![-122976177, -579415438, 204872], ![-60232373, 1494281919, 0]]]
    h := ![![![876, -4, -3], ![2526, 61, 0]], ![![421, 16, -4], ![1214, 81, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {294} * I101N2 =  Ideal.span {B.equivFun.symm ![66, -13, 2]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E101RS2 


noncomputable def E103RS1 : RelationCertificate Table 100842 ![![103, 0, 0], ![-17, 1, 0]]
  ![-79728, -564, -2759] ![![100842, 0, 0], ![49890, 1, 0]] where
    su := ![![10386726, 0, 0], ![-1714314, 100842, 0]]
    hsu := by decide
    w := ![![-8039930976, -56874888, -278223078], ![-3977712690, -28134918, -137649330]]
    hw := by decide
    g := ![![![243231241001264334, -61712778014453222652760, -6184884547938321632], ![-491640104330517097, 124739225516639246002809, 0]], ![![-40932110183797131, 10385319825841139545944, 1040821790605490753], ![82735535280706961, -20991710201647779702802, 0]]]
    h := ![![![-139233991122, 8402954552, -62564683], ![-843594176814, 1288831918, 0]], ![![-68885269837, 4157316679, -30953545], ![-417363691398, 637642754, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {100842} * I103N1 =  Ideal.span {B.equivFun.symm ![-79728, -564, -2759]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 2401 ![![107, 0, 0], ![41, 1, 0]]
  ![-3683, 9, -122] ![![2401, 0, 0], ![-531, 1, 0]] where
    su := ![![256907, 0, 0], ![98441, 2401, 0]]
    hsu := by decide
    w := ![![-8842883, 21609, -292922], ![1952013, -4802, 64827]]
    hw := by decide
    g := ![![![-26870638456407199, -305989370120420849925, 2881256315670995771], ![-121499817201193380, -1383579282785212169234, 0]], ![![-10246000458260890, -116676320570612230672, 1098647268044083273], ![-46328902260422593, -527570418114768787695, 0]]]
    h := ![![![-46948, -1389, -31], ![122433, 639, 0]], ![![10294, 257, 1], ![-26845, -16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {2401} * I107N1 =  Ideal.span {B.equivFun.symm ![-3683, 9, -122]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 42 ![![109, 0, 0], ![37, 1, 0]]
  ![-276, -1, -9] ![![42, 0, 0], ![18, 0, 1]] where
    su := ![![4578, 0, 0], ![1554, 42, 0]]
    hsu := by decide
    w := ![![-11592, -42, -378], ![-4998, -42, -168]]
    hw := by decide
    g := ![![![-8741063, 4138253, 89143], ![-3743999, 14483888, 0]], ![![-3036172, 1437402, 30963], ![-1300445, 5030908, 0]]]
    h := ![![![-291422, -9067, -161], ![858506, 3508, 0]], ![![-125648, -3921, -71], ![370149, 1547, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {42} * I109N0 =  Ideal.span {B.equivFun.symm ![-276, -1, -9]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 294 ![![109, 0, 0], ![-34, 1, 0]]
  ![414, 12, 17] ![![294, 0, 0], ![-90, 1, 0]] where
    su := ![![32046, 0, 0], ![-9996, 294, 0]]
    hsu := by decide
    w := ![![121716, 3528, 4998], ![-36750, -1176, -1470]]
    hw := by decide
    g := ![![![26201381, 27521919438, -1529011698], ![85591177, 89905887844, 0]], ![![-8293066, -8711065959, 483953228], ![-27090682, -28456449807, 0]]]
    h := ![![![4480822, -142552, 1583], ![14364976, -34506, 0]], ![![-1352873, 43054, -480], ![-4337148, 10463, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {294} * I109N1 =  Ideal.span {B.equivFun.symm ![414, 12, 17]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 117649 ![![109, 0, 0], ![-3, 1, 0]]
  ![89329, 255, 2946] ![![117649, 0, 0], ![-34145, 1, 0]] where
    su := ![![12823741, 0, 0], ![-352947, 117649, 0]]
    hsu := by decide
    w := ![![10509467521, 30000495, 346593954], ![-3050050325, -8706026, -100589895]]
    hw := by decide
    g := ![![![26741, 7251230239, -1061829], ![92138, 24984624000, 0]], ![![23783, -30238812, 4428], ![81946, -104189952, 0]]]
    h := ![![![32100981244, -10708265113, 13230539], ![1166335622089, -288425161, 0]], ![![-9316324358, 3107745224, -3839760], ![-338493109699, 83706597, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {117649} * I109N2 =  Ideal.span {B.equivFun.symm ![89329, 255, 2946]} * (J0 ^ 6*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_0 E109RS2 


noncomputable def E113RS0 : RelationCertificate Table 6 ![![113, 0, 0], ![36, 1, 0]]
  ![12, 0, 1] ![![6, 0, 0], ![0, 1, 0]] where
    su := ![![678, 0, 0], ![216, 6, 0]]
    hsu := by decide
    w := ![![72, 0, 6], ![30, -18, 0]]
    hw := by decide
    g := ![![![9, 659, -2], ![-3953, 3, 0]], ![![3, 210, -4], ![-1260, 5, 0]]]
    h := ![![![60, -20, -3], ![-188, 68, 0]], ![![-35, -1, 0], ![110, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {6} * I113N0 =  Ideal.span {B.equivFun.symm ![12, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 16807 ![![113, 0, 0], ![-29, 1, 0]]
  ![-5993, -222, -192] ![![16807, 0, 0], ![-531, 1, 0]] where
    su := ![![1899191, 0, 0], ![-487403, 16807, 0]]
    hsu := by decide
    w := ![![-100724351, -3731154, -3226944], ![3176523, 117649, 100842]]
    hw := by decide
    g := ![![![2289740, 1219240606281, -11480608386], ![72473937, 38590917028698, 0]], ![![-590771, -314642737105, 2962737648], ![-18698848, -9958946329986, 0]]]
    h := ![![![-78922, 2847, -24], ![-307317, 504, 0]], ![![2518, -69, -3], ![9805, 69, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {16807} * I113N1 =  Ideal.span {B.equivFun.symm ![-5993, -222, -192]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 14406 ![![113, 0, 0], ![-7, 1, 0]]
  ![-1002, 37, 32] ![![14406, 0, 0], ![-3090, 0, 1]] where
    su := ![![1627878, 0, 0], ![-100842, 14406, 0]]
    hsu := by decide
    w := ![![-14434812, 533022, 460992], ![3097290, -115248, -100842]]
    hw := by decide
    g := ![![![-518094, 56451997, -8], ![115219, 260656240, 0]], ![![32351, -3364481, 0], ![1, -15534844, 0]]]
    h := ![![![-102812396, 14742562, -39341], ![-1659685678, 889113, 0]], ![![22060561, -3163319, 8436], ![356120454, -190655, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {14406} * I113N2 =  Ideal.span {B.equivFun.symm ![-1002, 37, 32]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E113RS2 


noncomputable def E127RS0 : RelationCertificate Table 823543 ![![127, 0, 0], ![58, 1, 0]]
  ![-215647, 10, -6805] ![![823543, 0, 0], ![83504, 1, 0]] where
    su := ![![104589961, 0, 0], ![47765494, 823543, 0]]
    hsu := by decide
    w := ![![-177594577321, 8235430, -5604210115], ![-18007591238, 823543, -568244670]]
    hw := by decide
    g := ![![![10492982618171, -86100661988485487415, -5155481293627320], ![-103485131063379, 849152106199544798971, 0]], ![![4836000019892, -39682025695728541727, -2376055380328275], ![-47694169912602, 391356755216337715671, 0]]]
    h := ![![![-3291437, -70192, -1215], ![7203394, 29500, 0]], ![![-333790, -7139, -125], ![730508, 3037, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {823543} * I127N0 =  Ideal.span {B.equivFun.symm ![-215647, 10, -6805]} * (J0 ^ 7*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_0 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 4941258 ![![127, 0, 0], ![-40, 1, 0]]
  ![20472, -6665, 6046] ![![4941258, 0, 0], ![-2466516, 0, 1]] where
    su := ![![627539766, 0, 0], ![-197650320, 4941258, 0]]
    hsu := by decide
    w := ![![101157433776, -32933484570, 29874845868], ![-50494715502, 16439565366, -14912716644]]
    hw := by decide
    g := ![![![8812253, -724468028920, 0], ![1451, -1451334555952, 0]], ![![-226549, 221400898682, -1], ![4940818, 443534789872, 0]]]
    h := ![![![463576, -12401, 143], ![1471342, -2423, 0]], ![![-231317, 6209, -74], ![-734176, 1276, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {4941258} * I127N1 =  Ideal.span {B.equivFun.symm ![20472, -6665, 6046]} * (J0 ^ 7*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_2 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 14406 ![![127, 0, 0], ![-18, 1, 0]]
  ![2658, 60, -13] ![![14406, 0, 0], ![6672, 1, 0]] where
    su := ![![1829562, 0, 0], ![-259308, 14406, 0]]
    hsu := by decide
    w := ![![38291148, 864360, -187278], ![17733786, 403368, -86436]]
    hw := by decide
    g := ![![![365134826170, -13793713465804732, -10337015527976], ![-788389134563, 29783009139204452, 0]], ![![-52470167200, 1982167486263264, 1485437270779], ![113292150582, -4279841864568455, 0]]]
    h := ![![![699760002, -39628444, 209136], ![4937195422, -5312057, 0]], ![![324079855, -18353121, 96857], ![2286563353, -2460169, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {14406} * I127N2 =  Ideal.span {B.equivFun.symm ![2658, 60, -13]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E127RS2 


noncomputable def E137RS1 : RelationCertificate Table 34588806 ![![137, 0, 0], ![-51, 1, 0]]
  ![339888, 13889, 19280] ![![34588806, 0, 0], ![12357258, 0, 1]] where
    su := ![![4738666422, 0, 0], ![-1764029106, 34588806, 0]]
    hsu := by decide
    w := ![![11756320093728, 480403926534, 666872179680], ![4200084123774, 171629655372, 238247695728]]
    hw := by decide
    g := ![![![-110742213, -50705465652762, 1], ![-34587841, 141928393212705, 0]], ![![31104890, 17902333889018, -1], ![34588431, -50109972384945, 0]]]
    h := ![![![7882482, -167355, 1410], ![21167846, -34778, 0]], ![![2816150, -59793, 504], ![7562571, -12432, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {34588806} * I137N1 =  Ideal.span {B.equivFun.symm ![339888, 13889, 19280]} * (J0 ^ 8*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_2 E137RS1 
