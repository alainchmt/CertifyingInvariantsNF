import IdealArithmetic.Examples.NF3_1_343980_3.PrimesBelow3_1_343980_3F2
import IdealArithmetic.Examples.NF3_1_343980_3.ClassGroupData3_1_343980_3

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 55 ![![83, 0, 0], ![-35, 1, 0]]
  ![-28523, -11413, -1454] ![![55, 0, 0], ![8, 1, 0]] where
    su := ![![4565, 0, 0], ![-1925, 55, 0]]
    hsu := by decide
    w := ![![-1568765, -627715, -79970], ![-452100, -180895, -23045]]
    hw := by decide
    g := ![![![169821, -65600512, -8202714], ![-1168015, 451149429, 0]], ![![-68327, 26393528, 3300257], ![469994, -181514211, 0]]]
    h := ![![![-354076, 11001, -47], ![-838851, 2447, 0]], ![![-102030, 3186, -14], ![-241722, 743, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {55} * I83N1 =  Ideal.span {B.equivFun.symm ![-28523, -11413, -1454]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E83RS1 


noncomputable def E101RS1 : RelationCertificate Table 5 ![![101, 0, 0], ![9, 1, 0]]
  ![9, 1, 0] ![![5, 0, 0], ![-26, -4, 1]] where
    su := ![![505, 0, 0], ![45, 5, 0]]
    hsu := by decide
    w := ![![45, 5, 0], ![-80, -20, 5]]
    hw := by decide
    g := ![![![13, -1, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![18, 2, 0], ![-201, 0, 0]], ![![-62, -7, 0], ![694, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {5} * I101N1 =  Ideal.span {B.equivFun.symm ![9, 1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 121 ![![103, 0, 0], ![25, 1, 0]]
  ![33, 31, 3] ![![121, 0, 0], ![30, 1, 0]] where
    su := ![![12463, 0, 0], ![3025, 121, 0]]
    hsu := by decide
    w := ![![3993, 3751, 363], ![1452, 1089, 121]]
    hw := by decide
    g := ![![![-93, 32216, 1074], ![367, -129950, 0]], ![![-23, 9089, 303], ![91, -36662, 0]]]
    h := ![![![186, 7, 0], ![-765, 3, 0]], ![![54, 2, 0], ![-222, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {121} * I103N1 =  Ideal.span {B.equivFun.symm ![33, 31, 3]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 55 ![![107, 0, 0], ![30, 1, 0]]
  ![55, 14, 1] ![![55, 0, 0], ![-1, 1, 1]] where
    su := ![![5885, 0, 0], ![1650, 55, 0]]
    hsu := by decide
    w := ![![3025, 770, 55], ![2255, 825, 110]]
    hw := by decide
    g := ![![![8229, 2192, 55], ![-76, -2940, 0]], ![![2369, 630, 15], ![23, -846, 0]]]
    h := ![![![335, 11, 0], ![-1193, 1, 0]], ![![253, 8, 0], ![-901, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {55} * I107N0 =  Ideal.span {B.equivFun.symm ![55, 14, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 121 ![![107, 0, 0], ![-18, 1, 0]]
  ![-1639, -656, -83] ![![121, 0, 0], ![30, 1, 0]] where
    su := ![![12947, 0, 0], ![-2178, 121, 0]]
    hsu := by decide
    w := ![![-198319, -79376, -10043], ![-61952, -24805, -3146]]
    hw := by decide
    g := ![![![9, -4279, -143], ![17, 17262, 0]], ![![-28, 717, 24], ![102, -2896, 0]]]
    h := ![![![-2177, 118, -1], ![-12850, 24, 0]], ![![-676, 49, -1], ![-3990, 81, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {121} * I107N1 =  Ideal.span {B.equivFun.symm ![-1639, -656, -83]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 5 ![![107, 0, 0], ![-12, 1, 0]]
  ![-7043, -2818, -359] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![535, 0, 0], ![-60, 5, 0]]
    hsu := by decide
    w := ![![-35215, -14090, -1795], ![-41200, -16485, -2100]]
    hw := by decide
    g := ![![![-533, -10, -14], ![216, 133, 0]], ![![76, 2, 1], ![-29, -13, 0]]]
    h := ![![![-8605, 693, -4], ![-76141, 69, 0]], ![![-10072, 815, -5], ![-89122, 115, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {5} * I107N2 =  Ideal.span {B.equivFun.symm ![-7043, -2818, -359]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E107RS2 


noncomputable def E109RS1 : RelationCertificate Table 11 ![![109, 0, 0], ![-16, 1, 0]]
  ![407, 113, -21] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![1199, 0, 0], ![-176, 11, 0]]
    hsu := by decide
    w := ![![4477, 1243, -231], ![-4455, -814, 176]]
    hw := by decide
    g := ![![![400, -1049, 439], ![-193, -4575, 0]], ![![-27, 156, -59], ![25, 630, 0]]]
    h := ![![![75811, -4820, 5], ![516437, -566, 0]], ![![-75417, 4811, -6], ![-513753, 670, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {11} * I109N1 =  Ideal.span {B.equivFun.symm ![407, 113, -21]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 605 ![![113, 0, 0], ![19, 1, 0]]
  ![-9911, -1163, 309] ![![605, 0, 0], ![219, 1, 1]] where
    su := ![![68365, 0, 0], ![11495, 605, 0]]
    hsu := by decide
    w := ![![-5996155, -703615, 186945], ![-2302025, -252890, 69575]]
    hw := by decide
    g := ![![![2034622238, 3902868372, 13730163], ![742973575, -9049725536, 0]], ![![450071756, 863340169, 3037202], ![164350843, -2001858848, 0]]]
    h := ![![![-9925, -561, 1], ![58506, 196, 0]], ![![-3833, -223, 0], ![22596, 115, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {605} * I113N1 =  Ideal.span {B.equivFun.symm ![-9911, -1163, 309]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 55 ![![113, 0, 0], ![-20, 1, 0]]
  ![-627, -247, -31] ![![55, 0, 0], ![8, 1, 0]] where
    su := ![![6215, 0, 0], ![-1100, 55, 0]]
    hsu := by decide
    w := ![![-34485, -13585, -1705], ![-9790, -3905, -495]]
    hw := by decide
    g := ![![![3, -515, -65], ![26, 3553, 0]], ![![-8, 86, 11], ![43, -600, 0]]]
    h := ![![![-2439, 134, -1], ![-13749, 82, 0]], ![![-666, 51, -1], ![-3754, 104, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {55} * I113N2 =  Ideal.span {B.equivFun.symm ![-627, -247, -31]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E113RS2 


noncomputable def E127RS1 : RelationCertificate Table 55 ![![127, 0, 0], ![-46, 1, 0]]
  ![-3201, -1281, -163] ![![55, 0, 0], ![8, 1, 0]] where
    su := ![![6985, 0, 0], ![-2530, 55, 0]]
    hsu := by decide
    w := ![![-176055, -70455, -8965], ![-50710, -20295, -2585]]
    hw := by decide
    g := ![![![836199, -322862541, -40370884], ![-5748564, 2220398560, 0]], ![![-302518, 116800271, 14604761], ![2079692, -803261832, 0]]]
    h := ![![![-90467, 2127, -5], ![-249698, 472, 0]], ![![-25994, 637, -2], ![-71746, 207, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {55} * I127N1 =  Ideal.span {B.equivFun.symm ![-3201, -1281, -163]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 121 ![![131, 0, 0], ![48, 1, 0]]
  ![-319, 441, -51] ![![121, 0, 0], ![30, 1, 0]] where
    su := ![![15851, 0, 0], ![5808, 121, 0]]
    hsu := by decide
    w := ![![-38599, 53361, -6171], ![-17424, 10769, -1089]]
    hw := by decide
    g := ![![![8432653, -4368360599, -145621386], ![-34011328, 17620188276, 0]], ![![3129084, -1620958013, -54035409], ![-12620480, 6538284732, 0]]]
    h := ![![![-915557, -23660, -96], ![2498701, 12525, 0]], ![![-416496, -10737, -43], ![1136684, 5624, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {121} * I131N1 =  Ideal.span {B.equivFun.symm ![-319, 441, -51]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 5 ![![137, 0, 0], ![38, 1, 0]]
  ![-23, 3, 0] ![![5, 0, 0], ![-26, -4, 1]] where
    su := ![![685, 0, 0], ![190, 5, 0]]
    hsu := by decide
    w := ![![-115, 15, 0], ![1060, 140, -35]]
    hw := by decide
    g := ![![![25, 13, 2], ![-1, 0, 0]], ![![0, 3, 1], ![-2, 0, 0]]]
    h := ![![![-2357, -100, -1], ![8497, 137, 0]], ![![21656, 610, 1], ![-78070, -144, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {5} * I137N1 =  Ideal.span {B.equivFun.symm ![-23, 3, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E137RS1 
