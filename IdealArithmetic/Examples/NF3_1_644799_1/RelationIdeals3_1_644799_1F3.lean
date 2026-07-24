import IdealArithmetic.Examples.NF3_1_644799_1.PrimesBelow3_1_644799_1F3
import IdealArithmetic.Examples.NF3_1_644799_1.ClassGroupData3_1_644799_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 625 ![![139, 0, 0], ![-68, 1, 0]]
  ![-286, 26, 49] ![![625, 0, 0], ![-187, -171, 1]] where
    su := ![![86875, 0, 0], ![-42500, 625, 0]]
    hsu := by decide
    w := ![![-178750, 16250, 30625], ![1365625, 43750, -74375]]
    hw := by decide
    g := ![![![-428, 145, -39], ![308, 0, 0]], ![![285, -45, 22], ![-38, 0, 0]]]
    h := ![![![11970, 318800, -40985], ![-3454, 632996, 0]], ![![-90844, -2429232, 312304], ![27068, -4823375, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {625} * I139N1 =  Ideal.span {B.equivFun.symm ![-286, 26, 49]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E139RS1 


noncomputable def E151RS1 : RelationCertificate Table 25 ![![151, 0, 0], ![-14, 1, 0]]
  ![-14, 1, 0] ![![25, 0, 0], ![-12, 4, 1]] where
    su := ![![3775, 0, 0], ![-350, 25, 0]]
    hsu := by decide
    w := ![![-350, 25, 0], ![0, -75, 25]]
    hw := by decide
    g := ![![![1, -3, -1], ![16, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-742, -4033, 2268], ![152, -38052, 0]], ![![14, 8, -5], ![133, 84, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {25} * I151N1 =  Ideal.span {B.equivFun.symm ![-14, 1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E151RS1 


noncomputable def E157RS0 : RelationCertificate Table 625 ![![157, 0, 0], ![24, 1, 0]]
  ![152, 63, 47] ![![625, 0, 0], ![-187, -171, 1]] where
    su := ![![98125, 0, 0], ![15000, 625, 0]]
    hsu := by decide
    w := ![![95000, 39375, 29375], ![1243750, -25000, -129375]]
    hw := by decide
    g := ![![![867, -125, 66], ![-77, 0, 0]], ![![142, 55, 5], ![232, 0, 0]]]
    h := ![![![6329, -47271, -19336], ![768, 337311, 0]], ![![83542, -622632, -254691], ![8944, 4442920, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N0 : Ideal.span {625} * I157N0 =  Ideal.span {B.equivFun.symm ![152, 63, 47]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E157RS0 


noncomputable def E157RS1 : RelationCertificate Table 5 ![![157, 0, 0], ![66, 1, 0]]
  ![47, 0, -4] ![![5, 0, 0], ![-2, -1, 1]] where
    su := ![![785, 0, 0], ![330, 5, 0]]
    hsu := by decide
    w := ![![235, 0, -20], ![-370, 25, 55]]
    hw := by decide
    g := ![![![-409, 82, -62], ![138, 0, 0]], ![![-142, 29, -22], ![50, 0, 0]]]
    h := ![![![39629, -941323, -132364], ![10687, 2309016, 0]], ![![-62480, 1483534, 208607], ![-16785, -3639032, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {5} * I157N1 =  Ideal.span {B.equivFun.symm ![47, 0, -4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 6875 ![![163, 0, 0], ![13, 1, 0]]
  ![-6001, 701, -446] ![![6875, 0, 0], ![1688, 454, 1]] where
    su := ![![1120625, 0, 0], ![89375, 6875, 0]]
    hsu := by decide
    w := ![![-41256875, 4819375, -3066250], ![20432500, -2371875, 1498750]]
    hw := by decide
    g := ![![![-221, -199, -480], ![1630, 807, 0]], ![![-1567, -438, -58], ![6468, 96, 0]]]
    h := ![![![-17016808276, 62685350076, 51283131727], ![-972595974, -928794496883, 0]], ![![8427543188, -31044805065, -25397877265], ![481676523, 459983777157, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {6875} * I163N1 =  Ideal.span {B.equivFun.symm ![-6001, 701, -446]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 25 ![![167, 0, 0], ![-6, 1, 0]]
  ![-23, 1, 3] ![![25, 0, 0], ![-12, 4, 1]] where
    su := ![![4175, 0, 0], ![-150, 25, 0]]
    hsu := by decide
    w := ![![-575, 25, 75], ![-2025, -150, 25]]
    hw := by decide
    g := ![![![38, -3, 4], ![-16, 0, 0]], ![![3, -2, -1], ![16, 0, 0]]]
    h := ![![![-236863, -632122, 711105], ![4791, -13194948, 0]], ![![-833469, -2224286, 2502209], ![16732, -46429878, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {25} * I167N1 =  Ideal.span {B.equivFun.symm ![-23, 1, 3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 5 ![![173, 0, 0], ![71, 1, 0]]
  ![122, 13, 2] ![![5, 0, 0], ![-2, -1, 1]] where
    su := ![![865, 0, 0], ![355, 5, 0]]
    hsu := by decide
    w := ![![610, 65, 10], ![-2095, -145, 40]]
    hw := by decide
    g := ![![![-3347, 664, -502], ![1107, 0, 0]], ![![-1156, 230, -174], ![385, 0, 0]]]
    h := ![![![61235, -1561418, -203651], ![16202, 3914625, 0]], ![![-210658, 5367722, 700096], ![-55335, -13457400, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {5} * I173N1 =  Ideal.span {B.equivFun.symm ![122, 13, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E173RS1 


noncomputable def E179RS0 : RelationCertificate Table 125 ![![179, 0, 0], ![21, 1, 0]]
  ![76, 10, 3] ![![125, 0, 0], ![-62, -46, 1]] where
    su := ![![22375, 0, 0], ![2625, 125, 0]]
    hsu := by decide
    w := ![![9500, 1250, 375], ![16375, -3375, -4625]]
    hw := by decide
    g := ![![![-56, 33, -7], ![62, 0, 0]], ![![35, 30, -1], ![80, 0, 0]]]
    h := ![![![5717, -36565, -17319], ![481, 344456, 0]], ![![9859, -63159, -29915], ![966, 594972, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N0 : Ideal.span {125} * I179N0 =  Ideal.span {B.equivFun.symm ![76, 10, 3]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E179RS0 


noncomputable def E179RS1 : RelationCertificate Table 11 ![![179, 0, 0], ![60, 1, 0]]
  ![-2, -1, -2] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![1969, 0, 0], ![660, 11, 0]]
    hsu := by decide
    w := ![![-22, -11, -22], ![319, 0, -11]]
    hw := by decide
    g := ![![![-7538701, -10199416, 22857979], ![443463, -27937530, 0]], ![![-2571339, -3478871, 7796520], ![151263, -9529080, 0]]]
    h := ![![![107, -3178, -493], ![171, 9805, 0]], ![![-2708, 55283, 8578], ![-451, -170607, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {11} * I179N1 =  Ideal.span {B.equivFun.symm ![-2, -1, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E179RS1 


noncomputable def E179RS2 : RelationCertificate Table 1375 ![![179, 0, 0], ![-82, 1, 0]]
  ![-1301, -73, 41] ![![1375, 0, 0], ![-312, 79, 1]] where
    su := ![![246125, 0, 0], ![-112750, 1375, 0]]
    hsu := by decide
    w := ![![-1788875, -100375, 56375], ![-74250, -66000, -56375]]
    hw := by decide
    g := ![![![-682227985, -849263661, 1283476927], ![106943665, -2471831549, 0]], ![![306367775, 381377902, -576369705], ![-48023638, 1110022930, 0]]]
    h := ![![![-6904, -219287, 23494], ![2040, -467265, 0]], ![![-238, -8786, 941], ![166, -18720, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N2 : Ideal.span {1375} * I179N2 =  Ideal.span {B.equivFun.symm ![-1301, -73, 41]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E179RS2 


noncomputable def E181RS1 : RelationCertificate Table 3125 ![![181, 0, 0], ![58, 1, 0]]
  ![112, 13, 2] ![![3125, 0, 0], ![-812, 1079, 1]] where
    su := ![![565625, 0, 0], ![181250, 3125, 0]]
    hsu := by decide
    w := ![![350000, 40625, 6250], ![-471875, 84375, 131250]]
    hw := by decide
    g := ![![![437, -587, -1], ![1702, 0, 0]], ![![713, -949, -1], ![2749, 0, 0]]]
    h := ![![![10680, -213921, -34378], ![2434, 691380, 0]], ![![-14569, 289236, 46482], ![-2889, -934800, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {3125} * I181N1 =  Ideal.span {B.equivFun.symm ![112, 13, 2]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E181RS1 


noncomputable def E193RS1 : RelationCertificate Table 125 ![![193, 0, 0], ![63, 1, 0]]
  ![17, 1, -2] ![![125, 0, 0], ![-62, -46, 1]] where
    su := ![![24125, 0, 0], ![7875, 125, 0]]
    hsu := by decide
    w := ![![2125, 125, -250], ![-15250, -625, 0]]
    hw := by decide
    g := ![![![47, 36, -1], ![96, 0, 0]], ![![59, 44, -1], ![119, 0, 0]]]
    h := ![![![854453, -18588169, -2742377], ![182807, 58808751, 0]], ![![-6133175, 133413974, 19683027], ![-1310668, -422091579, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {125} * I193N1 =  Ideal.span {B.equivFun.symm ![17, 1, -2]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E193RS1 


noncomputable def E193RS2 : RelationCertificate Table 125 ![![193, 0, 0], ![-83, 1, 0]]
  ![97, 15, 6] ![![125, 0, 0], ![-62, -46, 1]] where
    su := ![![24125, 0, 0], ![-10375, 125, 0]]
    hsu := by decide
    w := ![![12125, 1875, 750], ![36250, -4375, -7250]]
    hw := by decide
    g := ![![![-129, 76, -16], ![143, 0, 0]], ![![113, 0, 7], ![31, 0, 0]]]
    h := ![![![3029980, 95688966, -10131330], ![-807183, 217260744, 0]], ![![9085506, 286928773, -30379366], ![-2420524, 651468620, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N2 : Ideal.span {125} * I193N2 =  Ideal.span {B.equivFun.symm ![97, 15, 6]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E193RS2 
