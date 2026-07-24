import IdealArithmetic.Examples.NF3_3_895700_1.PrimesBelow3_3_895700_1F2
import IdealArithmetic.Examples.NF3_3_895700_1.ClassGroupData3_3_895700_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 3249 ![![83, 0, 0], ![-28, 1, 0]]
  ![2342, -171, -67] ![![3249, 0, 0], ![-685, 1, 0]] where
    su := ![![269667, 0, 0], ![-90972, 3249, 0]]
    hsu := by decide
    w := ![![7609158, -555579, -217683], ![-1575765, 113715, 45486]]
    hw := by decide
    g := ![![![-17718437203, 13266337356764, -38733838725], ![7818859172, 62923121008738, 0]], ![![5355153550, -4009567499317, 11706768545], ![-2363141046, -19017645501346, 0]]]
    h := ![![![484776663, -17054991464, 1218531249], ![-369020935, -50569046867, 0]], ![![-100390340, 3531845900, -252340472], ![76418995, 10472129595, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {3249} * I83N1 =  Ideal.span {B.equivFun.symm ![2342, -171, -67]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E83RS1 


noncomputable def E89RS0 : RelationCertificate Table 361 ![![89, 0, 0], ![42, 1, 0]]
  ![1063, -38, -17] ![![361, 0, 0], ![37, 1, 0]] where
    su := ![![32129, 0, 0], ![15162, 361, 0]]
    hsu := by decide
    w := ![![383743, -13718, -6137], ![46569, -1805, -722]]
    hw := by decide
    g := ![![![748927461, 28298248054, 1529658261], ![155148732, -276103316115, 0]], ![![359283820, 13575551051, 733824715], ![74429791, -132455361060, 0]]]
    h := ![![![-12935890, -854398780, -40694059], ![-15704532, 1810885617, 0]], ![![-1569933, -103691159, -4938694], ![-1905898, 219771882, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {361} * I89N0 =  Ideal.span {B.equivFun.symm ![1063, -38, -17]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 3 ![![89, 0, 0], ![-40, 1, 0]]
  ![-74, 3, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![267, 0, 0], ![-120, 3, 0]]
    hsu := by decide
    w := ![![-222, 9, 3], ![-351, 9, 6]]
    hw := by decide
    g := ![![![-42, -1, 1], ![17, 0, 0]], ![![18, -3, 5], ![-4, -8, 0]]]
    h := ![![![2502, -149269, 7465], ![-2736, -332192, 0]], ![![3915, -235830, 11794], ![-4407, -524832, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {3} * I89N1 =  Ideal.span {B.equivFun.symm ![-74, 3, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 171 ![![89, 0, 0], ![-3, 1, 0]]
  ![85, 0, 1] ![![171, 0, 0], ![-1, 1, 0]] where
    su := ![![15219, 0, 0], ![-513, 171, 0]]
    hsu := by decide
    w := ![![14535, 0, 171], ![-513, 171, 0]]
    hw := by decide
    g := ![![![-944, 945, -1891], ![84, 161680, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-853762, 2566469, -1711411], ![57629, 76157790, 0]], ![![30306, -91094, 60744], ![-1957, -2703108, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {171} * I89N2 =  Ideal.span {B.equivFun.symm ![85, 0, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E89RS2 


noncomputable def E101RS1 : RelationCertificate Table 361 ![![101, 0, 0], ![-41, 1, 0]]
  ![2487, -76, -34] ![![361, 0, 0], ![37, 1, 0]] where
    su := ![![36461, 0, 0], ![-14801, 361, 0]]
    hsu := by decide
    w := ![![897807, -27436, -12274], ![106495, -3249, -1444]]
    hw := by decide
    g := ![![![9948, 376321, 20342], ![2169, -3671730, 0]], ![![-3974, -149848, -8100], ![-739, 1462050, 0]]]
    h := ![![![-10140, 581971, -28394], ![9933, 1433880, 0]], ![![-1185, 69031, -3368], ![1222, 170082, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {361} * I101N1 =  Ideal.span {B.equivFun.symm ![2487, -76, -34]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 3249 ![![103, 0, 0], ![-2, 1, 0]]
  ![15158, -513, -220] ![![3249, 0, 0], ![-685, 1, 0]] where
    su := ![![334647, 0, 0], ![-6498, 3249, 0]]
    hsu := by decide
    w := ![![49248342, -1666737, -714780], ![-10289583, 347643, 149454]]
    hw := by decide
    g := ![![![-69996356418, 52408418035001, -153017306692], ![30888252141, 248576614721125, 0]], ![![386377382, -289292175223, 844648840], ![-170499163, -1372132040582, 0]]]
    h := ![![![-262517, 525623, -525730], ![10288, 27074985, 0]], ![![54849, -109820, 109842], ![-2113, -5656840, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {3249} * I103N1 =  Ideal.span {B.equivFun.symm ![15158, -513, -220]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E103RS1 


noncomputable def E109RS1 : RelationCertificate Table 57 ![![109, 0, 0], ![11, 1, 0]]
  ![-229, 0, 2] ![![57, 0, 0], ![-1, 1, 0]] where
    su := ![![6213, 0, 0], ![627, 57, 0]]
    hsu := by decide
    w := ![![-13053, 0, 114], ![-627, -57, 0]]
    hw := by decide
    g := ![![![-28299195, 28299194, -56633230], ![993008, 1614047054, 0]], ![![-3185056, 3185056, -6374034], ![111776, 181659969, 0]]]
    h := ![![![-33, -232, -42], ![98, 2290, 0]], ![![-12, -12, -2], ![108, 109, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {57} * I109N1 =  Ideal.span {B.equivFun.symm ![-229, 0, 2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E109RS1 


noncomputable def E113RS0 : RelationCertificate Table 1083 ![![113, 0, 0], ![4, 1, 0]]
  ![4508, -171, -67] ![![1083, 0, 0], ![398, 1, 0]] where
    su := ![![122379, 0, 0], ![4332, 1083, 0]]
    hsu := by decide
    w := ![![4882164, -185193, -72561], ![1822689, -69312, -27075]]
    hw := by decide
    g := ![![![7821, 4121087, 20709], ![6895, -11213930, 0]], ![![-64, 160990, 809], ![1275, -438074, 0]]]
    h := ![![![-413950686, -1659697675, -829978663], ![-29340600, 46893794426, 0]], ![![-154542987, -619626065, -309861501], ![-10953895, 17507174794, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {1083} * I113N0 =  Ideal.span {B.equivFun.symm ![4508, -171, -67]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 9 ![![113, 0, 0], ![14, 1, 0]]
  ![-41, 0, 1] ![![9, 0, 0], ![-1, 1, 0]] where
    su := ![![1017, 0, 0], ![126, 9, 0]]
    hsu := by decide
    w := ![![-369, 0, 9], ![-387, 45, 0]]
    hw := by decide
    g := ![![![-40, 15, -27], ![8, 124, 0]], ![![-7, 2, -5], ![9, 23, 0]]]
    h := ![![![36240, 523148, 74747], ![9146, -4223205, 0]], ![![38049, 549275, 78480], ![9610, -4434120, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {9} * I113N1 =  Ideal.span {B.equivFun.symm ![-41, 0, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 19 ![![113, 0, 0], ![-19, 1, 0]]
  ![-67, 0, 1] ![![19, 0, 0], ![-1, 1, 0]] where
    su := ![![2147, 0, 0], ![-361, 19, 0]]
    hsu := by decide
    w := ![![-1273, 0, 19], ![-361, 19, 0]]
    hw := by decide
    g := ![![![-375, 376, -759], ![57, 7210, 0]], ![![60, -60, 120], ![1, -1140, 0]]]
    h := ![![![-1544, 31335, -3299], ![631, 186394, 0]], ![![-430, 8890, -936], ![227, 52884, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {19} * I113N2 =  Ideal.span {B.equivFun.symm ![-67, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E113RS2 


noncomputable def E127RS1 : RelationCertificate Table 3 ![![127, 0, 0], ![-17, 1, 0]]
  ![-68, 3, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![381, 0, 0], ![-51, 3, 0]]
    hsu := by decide
    w := ![![-204, 9, 3], ![-357, 15, 6]]
    hw := by decide
    g := ![![![-34906, 34883, -85269], ![23263, 127904, 0]], ![![3740, -3738, 9136], ![-2491, -13704, 0]]]
    h := ![![![-3634, 64243, -7559], ![1091, 479997, 0]], ![![-6374, 112424, -13228], ![1800, 839979, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {3} * I127N1 =  Ideal.span {B.equivFun.symm ![-68, 3, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E127RS1 


noncomputable def E131RS0 : RelationCertificate Table 57 ![![131, 0, 0], ![5, 1, 0]]
  ![-143, 0, 1] ![![57, 0, 0], ![-1, 1, 0]] where
    su := ![![7467, 0, 0], ![285, 57, 0]]
    hsu := by decide
    w := ![![-8151, 0, 57], ![-285, -57, 0]]
    hw := by decide
    g := ![![![-23378951, 23378950, -46786683], ![820318, 1333420465, 0]], ![![-1276029, 1276029, -2553630], ![44801, 72778455, 0]]]
    h := ![![![4337, 21774, 8711], ![456, -570570, 0]], ![![147, 759, 304], ![130, -19912, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {57} * I131N0 =  Ideal.span {B.equivFun.symm ![-143, 0, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E131RS0 


noncomputable def E131RS2 : RelationCertificate Table 3249 ![![131, 0, 0], ![-29, 1, 0]]
  ![-1397, 342, 58] ![![3249, 0, 0], ![-685, 1, 0]] where
    su := ![![425619, 0, 0], ![-94221, 3249, 0]]
    hsu := by decide
    w := ![![-4538853, 1111158, 188442], ![932463, -230679, -38988]]
    hw := by decide
    g := ![![![40524, -30318781, 88522], ![-17725, -143803996, 0]], ![![-8353, 6385569, -18644], ![4596, 30287180, 0]]]
    h := ![![![38037723, -1216640408, 83915558], ![-17707790, -5496469020, 0]], ![![-7816650, 250016542, -17244436], ![3638935, 1129510552, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {3249} * I131N2 =  Ideal.span {B.equivFun.symm ![-1397, 342, 58]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E131RS2 


noncomputable def E137RS1 : RelationCertificate Table 9 ![![137, 0, 0], ![-64, 1, 0]]
  ![-272, 9, 4] ![![9, 0, 0], ![-1, 1, 0]] where
    su := ![![1233, 0, 0], ![-576, 9, 0]]
    hsu := by decide
    w := ![![-2448, 81, 36], ![-1431, 63, 18]]
    hw := by decide
    g := ![![![-282, 239, -482], ![64, 2174, 0]], ![![129, -112, 224], ![-18, -1010, 0]]]
    h := ![![![-189491, 18900427, -590690], ![226598, 40462267, 0]], ![![-110742, 11049401, -345324], ![132550, 23654695, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {9} * I137N1 =  Ideal.span {B.equivFun.symm ![-272, 9, 4]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E137RS1 
