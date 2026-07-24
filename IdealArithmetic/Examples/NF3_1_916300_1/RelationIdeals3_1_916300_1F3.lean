import IdealArithmetic.Examples.NF3_1_916300_1.PrimesBelow3_1_916300_1F3
import IdealArithmetic.Examples.NF3_1_916300_1.ClassGroupData3_1_916300_1

set_option linter.all false

noncomputable section


noncomputable def E139RS0 : RelationCertificate Table 33 ![![139, 0, 0], ![21, 1, 0]]
  ![16, -20, 5] ![![33, 0, 0], ![15, 7, 1]] where
    su := ![![4587, 0, 0], ![693, 33, 0]]
    hsu := by decide
    w := ![![528, -660, 165], ![3300, -363, -264]]
    hw := by decide
    g := ![![![60, 145, -22], ![79, 139, 0]], ![![26, 20, -3], ![19, 20, 0]]]
    h := ![![![82, 3, 0], ![-542, 5, 0]], ![![670, 12, -1], ![-4430, 131, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N0 : Ideal.span {33} * I139N0 =  Ideal.span {B.equivFun.symm ![16, -20, 5]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E139RS0 


noncomputable def E139RS1 : RelationCertificate Table 33 ![![139, 0, 0], ![42, 1, 0]]
  ![-115, -4, -2] ![![33, 0, 0], ![15, 7, 1]] where
    su := ![![4587, 0, 0], ![1386, 33, 0]]
    hsu := by decide
    w := ![![-3795, -132, -66], ![-4785, -231, -99]]
    hw := by decide
    g := ![![![-566, 174, -28], ![-182, 139, 0]], ![![-163, 53, -8], ![-62, 41, 0]]]
    h := ![![![-97549, -2658, -8], ![322838, 1110, 0]], ![![-123055, -3349, -10], ![407250, 1387, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {33} * I139N1 =  Ideal.span {B.equivFun.symm ![-115, -4, -2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E139RS1 


noncomputable def E139RS2 : RelationCertificate Table 33 ![![139, 0, 0], ![-64, 1, 0]]
  ![-1, -1, 1] ![![33, 0, 0], ![15, 7, 1]] where
    su := ![![4587, 0, 0], ![-2112, 33, 0]]
    hsu := by decide
    w := ![![-33, -33, 33], ![1056, -198, -33]]
    hw := by decide
    g := ![![![-18449479, 6049220, -918073], ![-7130775, 4678400, 0]], ![![8465048, -2775528, 421233], ![3271784, -2146560, 0]]]
    h := ![![![29, 0, 0], ![63, 1, 0]], ![![1376, -22, 0], ![2988, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N2 : Ideal.span {33} * I139N2 =  Ideal.span {B.equivFun.symm ![-1, -1, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E139RS2 


noncomputable def E149RS1 : RelationCertificate Table 33 ![![149, 0, 0], ![46, 1, 0]]
  ![730, 25, 14] ![![33, 0, 0], ![9, 1, 0]] where
    su := ![![4917, 0, 0], ![1518, 33, 0]]
    hsu := by decide
    w := ![![24090, 825, 462], ![8712, 297, 165]]
    hw := by decide
    g := ![![![-237709, 30901028, 3436382], ![871586, -113400607, 0]], ![![-71798, 9332529, 1037834], ![263255, -34248522, 0]]]
    h := ![![![758046, 18545, 45], ![-2455394, -6691, 0]], ![![274092, 6693, 16], ![-887814, -2379, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {33} * I149N1 =  Ideal.span {B.equivFun.symm ![730, 25, 14]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E149RS1 


noncomputable def E151RS1 : RelationCertificate Table 11 ![![151, 0, 0], ![-26, 1, 0]]
  ![-49513, -1800, -942] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![1661, 0, 0], ![-286, 11, 0]]
    hsu := by decide
    w := ![![-544643, -19800, -10362], ![-45100, -1639, -858]]
    hw := by decide
    g := ![![![85, 968, -498], ![80, 5436, 0]], ![![-18, -166, 86], ![-11, -940, 0]]]
    h := ![![![-14806291, 584860, -599], ![-85988478, 89507, 0]], ![![-1226016, 48439, -50], ![-7120166, 7472, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {11} * I151N1 =  Ideal.span {B.equivFun.symm ![-49513, -1800, -942]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E151RS1 


noncomputable def E163RS1 : RelationCertificate Table 11 ![![163, 0, 0], ![-28, 1, 0]]
  ![38, -13, 0] ![![11, 0, 0], ![26, -4, 1]] where
    su := ![![1793, 0, 0], ![-308, 11, 0]]
    hsu := by decide
    w := ![![418, -143, 0], ![-1001, 121, 77]]
    hw := by decide
    g := ![![![123, 135, -11], ![290, 0, 0]], ![![-37, -18, 1], ![-37, 0, 0]]]
    h := ![![![12794, -457, 0], ![74478, 0, 0]], ![![-30541, 1120, -1], ![-177789, 170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {11} * I163N1 =  Ideal.span {B.equivFun.symm ![38, -13, 0]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E163RS1 


noncomputable def E191RS0 : RelationCertificate Table 11 ![![191, 0, 0], ![34, 1, 0]]
  ![4153, 151, 79] ![![11, 0, 0], ![26, -4, 1]] where
    su := ![![2101, 0, 0], ![374, 11, 0]]
    hsu := by decide
    w := ![![45683, 1661, 869], ![94820, 3443, 1804]]
    hw := by decide
    g := ![![![-12, -9, -7], ![47, 0, 0]], ![![-20, 2, -2], ![15, 0, 0]]]
    h := ![![![1179695, 36043, 40], ![-6626988, -7561, 0]], ![![2448676, 74813, 83], ![-13755544, -15689, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N0 : Ideal.span {11} * I191N0 =  Ideal.span {B.equivFun.symm ![4153, 151, 79]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E191RS0 


noncomputable def E191RS1 : RelationCertificate Table 9 ![![191, 0, 0], ![38, 1, 0]]
  ![208, -86, 5] ![![9, 0, 0], ![0, 1, 0]] where
    su := ![![1719, 0, 0], ![342, 9, 0]]
    hsu := by decide
    w := ![![1872, -774, 45], ![765, -27, -81]]
    hw := by decide
    g := ![![![4608, 165, 613731], ![23, -5522790, 0]], ![![987, 35, 135811], ![8, -1222130, 0]]]
    h := ![![![44364, 1204, 1], ![-222982, -186, 0]], ![![18135, 479, 0], ![-91150, -9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {9} * I191N1 =  Ideal.span {B.equivFun.symm ![208, -86, 5]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E191RS1 


noncomputable def E191RS2 : RelationCertificate Table 33 ![![191, 0, 0], ![-73, 1, 0]]
  ![-1517, 559, -13] ![![33, 0, 0], ![9, 1, 0]] where
    su := ![![6303, 0, 0], ![-2409, 33, 0]]
    hsu := by decide
    w := ![![-50061, 18447, -429], ![-15642, 4125, 429]]
    hw := by decide
    g := ![![![175364, -21083815, -2344424], ![-591070, 77374884, 0]], ![![-63265, 7594704, 844495], ![212915, -27871598, 0]]]
    h := ![![![-4070856, 62114, -87], ![-10651123, 16604, 0]], ![![-1271544, 19468, -28], ![-3326910, 5361, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N2 : Ideal.span {33} * I191N2 =  Ideal.span {B.equivFun.symm ![-1517, 559, -13]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E191RS2 


noncomputable def E193RS0 : RelationCertificate Table 11 ![![193, 0, 0], ![51, 1, 0]]
  ![-116, 133, -32] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![2123, 0, 0], ![561, 11, 0]]
    hsu := by decide
    w := ![![-1276, 1463, -352], ![-4664, 1122, 165]]
    hw := by decide
    g := ![![![-59491, -5238574, 2641377], ![-465413, -29049888, 0]], ![![-15842, -1414909, 713431], ![-125738, -7846272, 0]]]
    h := ![![![-1436, -70, -1], ![5432, 161, 0]], ![![-5182, -156, -1], ![19602, 208, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N0 : Ideal.span {11} * I193N0 =  Ideal.span {B.equivFun.symm ![-116, 133, -32]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E193RS0 


noncomputable def E193RS1 : RelationCertificate Table 3 ![![193, 0, 0], ![-36, 1, 0]]
  ![-11, -2, 2] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![579, 0, 0], ![-108, 3, 0]]
    hsu := by decide
    w := ![![-33, -6, 6], ![306, -105, 0]]
    hw := by decide
    g := ![![![1225, 40, 214], ![14, -572, 0]], ![![-210, -7, -39], ![-2, 105, 0]]]
    h := ![![![-95, 3, 0], ![-509, 2, 0]], ![![1470, -41, 0], ![7878, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {3} * I193N1 =  Ideal.span {B.equivFun.symm ![-11, -2, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E193RS1 


noncomputable def E193RS2 : RelationCertificate Table 99 ![![193, 0, 0], ![-16, 1, 0]]
  ![1937, 71, 37] ![![99, 0, 0], ![-18, 7, 1]] where
    su := ![![19107, 0, 0], ![-1584, 99, 0]]
    hsu := by decide
    w := ![![191763, 7029, 3663], ![21285, 693, 396]]
    hw := by decide
    g := ![![![4174, -1780, 235], ![-827, -2800, 0]], ![![-318, 136, -19], ![118, 220, 0]]]
    h := ![![![3097601, -194892, 81], ![37364691, -15596, 0]], ![![343847, -21634, 9], ![4147641, -1733, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N2 : Ideal.span {99} * I193N2 =  Ideal.span {B.equivFun.symm ![1937, 71, 37]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E193RS2 
