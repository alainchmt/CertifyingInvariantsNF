import IdealArithmetic.Examples.NF3_1_297332_1.PrimesBelow3_1_297332_1F2
import IdealArithmetic.Examples.NF3_1_297332_1.ClassGroupData3_1_297332_1

set_option linter.all false

noncomputable section


noncomputable def E89RS0 : RelationCertificate Table 100 ![![89, 0, 0], ![21, 1, 0]]
  ![-200597, -65581, -13071] ![![100, 0, 0], ![2, -2, 1]] where
    su := ![![8900, 0, 0], ![2100, 100, 0]]
    hsu := by decide
    w := ![![-20059700, -6558100, -1307100], ![-6474800, -2116800, -421900]]
    hw := by decide
    g := ![![![-22328985939141, -5373023547739, 583479640054], ![-333284451417, 14503669888359, 0]], ![![-5017749650485, -1207421022263, 131119020269], ![-74895382347, 3259251661116, 0]]]
    h := ![![![-739306, -37831, -337], ![3123697, 8461, 0]], ![![-238624, -12213, -109], ![1008228, 2741, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {100} * I89N0 =  Ideal.span {B.equivFun.symm ![-200597, -65581, -13071]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 5 ![![89, 0, 0], ![-13, 1, 0]]
  ![171, -7, -2] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![445, 0, 0], ![-65, 5, 0]]
    hsu := by decide
    w := ![![855, -35, -10], ![-650, 115, -10]]
    hw := by decide
    g := ![![![165, 78, 4], ![-49, 20, 0]], ![![-5, -3, 0], ![3, -1, 0]]]
    h := ![![![11439, -893, 2], ![78300, -90, 0]], ![![-8684, 681, -2], ![-59442, 88, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {5} * I89N1 =  Ideal.span {B.equivFun.symm ![171, -7, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 2 ![![89, 0, 0], ![-8, 1, 0]]
  ![17, 5, 1] ![![2, 0, 0], ![-22, -2, 1]] where
    su := ![![178, 0, 0], ![-16, 2, 0]]
    hsu := by decide
    w := ![![34, 10, 2], ![88, 38, 10]]
    hw := by decide
    g := ![![![29801, -17532, 59352], ![-280585, -40470, 0]], ![![-2348, 1385, -4686], ![22152, 3195, 0]]]
    h := ![![![273, -30, -1], ![3035, 45, 0]], ![![684, -81, -1], ![7604, 47, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {2} * I89N2 =  Ideal.span {B.equivFun.symm ![17, 5, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E89RS2 


noncomputable def E101RS1 : RelationCertificate Table 10 ![![101, 0, 0], ![38, 1, 0]]
  ![79, -43, 7] ![![10, 0, 0], ![-18, -2, 1]] where
    su := ![![1010, 0, 0], ![380, 10, 0]]
    hsu := by decide
    w := ![![790, -430, 70], ![-10200, -840, 370]]
    hw := by decide
    g := ![![![1509881137659, 163117082692, 106664727125], ![-2739742991581, -418273930047, 0]], ![![553124951460, 59755782219, 39075209655], ![-1003668548070, -153229112863, 0]]]
    h := ![![![219, -15, -1], ![-580, 54, 0]], ![![-2944, -104, -1], ![7798, 69, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {10} * I101N1 =  Ideal.span {B.equivFun.symm ![79, -43, 7]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 100 ![![107, 0, 0], ![22, 1, 0]]
  ![107, 11, 1] ![![100, 0, 0], ![2, -2, 1]] where
    su := ![![10700, 0, 0], ![2200, 100, 0]]
    hsu := by decide
    w := ![![10700, 1100, 100], ![1600, 200, 100]]
    hw := by decide
    g := ![![![198900928266149, 47861527350820, -5197488248991], ![2968813135817, -129195002940821, 0]], ![![39036704508280, 9393401613537, -1020069713751], ![582665360824, -25356076503569, 0]]]
    h := ![![![171557, 8227, 39], ![-834386, -2086, 0]], ![![25632, 1220, 5], ![-124664, -267, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {100} * I107N1 =  Ideal.span {B.equivFun.symm ![107, 11, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E107RS1 


noncomputable def E113RS1 : RelationCertificate Table 20 ![![113, 0, 0], ![55, 1, 0]]
  ![-1457, -201, 69] ![![20, 0, 0], ![-18, -2, 1]] where
    su := ![![2260, 0, 0], ![1100, 20, 0]]
    hsu := by decide
    w := ![![-29140, -4020, 1380], ![-25980, -20, 520]]
    hw := by decide
    g := ![![![322194704, 35376215, -553705], ![-293540527, -76153473, 0]], ![![153969160, 16905437, -264608], ![-140275991, -36391932, 0]]]
    h := ![![![-19534, -456, -3], ![40107, 204, 0]], ![![-17428, -433, -4], ![35783, 239, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {20} * I113N1 =  Ideal.span {B.equivFun.symm ![-1457, -201, 69]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E113RS1 


noncomputable def E127RS1 : RelationCertificate Table 20 ![![127, 0, 0], ![-62, 1, 0]]
  ![191, 63, 13] ![![20, 0, 0], ![-18, -2, 1]] where
    su := ![![2540, 0, 0], ![-1240, 20, 0]]
    hsu := by decide
    w := ![![3820, 1260, 260], ![2260, 780, 160]]
    hw := by decide
    g := ![![![132519305164, 14550355896, -227718549], ![-120733796135, -31322041773, 0]], ![![-65042218188, -7141506075, 111767258], ![59257735376, 15373270131, 0]]]
    h := ![![![294543, -5460, 23], ![603335, -1454, 0]], ![![174237, -3180, 12], ![356903, -758, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {20} * I127N1 =  Ideal.span {B.equivFun.symm ![191, 63, 13]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS1 


noncomputable def E131RS0 : RelationCertificate Table 5 ![![131, 0, 0], ![55, 1, 0]]
  ![97, 31, 6] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![655, 0, 0], ![275, 5, 0]]
    hsu := by decide
    w := ![![485, 155, 30], ![730, 245, 50]]
    hw := by decide
    g := ![![![-71, -208, 204], ![-11, -502, 0]], ![![-25, -88, 86], ![-2, -212, 0]]]
    h := ![![![13752, 304, 2], ![-32753, -128, 0]], ![![20776, 431, 2], ![-49482, -126, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {5} * I131N0 =  Ideal.span {B.equivFun.symm ![97, 31, 6]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E131RS0 


noncomputable def E131RS1 : RelationCertificate Table 100 ![![131, 0, 0], ![-51, 1, 0]]
  ![-93, 11, 1] ![![100, 0, 0], ![2, -2, 1]] where
    su := ![![13100, 0, 0], ![-5100, 100, 0]]
    hsu := by decide
    w := ![![-9300, 1100, 100], ![1200, 600, -100]]
    hw := by decide
    g := ![![![-474250449969, -114118878579, 12392657803], ![-7078704805, 308046768873, 0]], ![![185834411197, 44717331547, -4856046560], ![2773781143, -120707718714, 0]]]
    h := ![![![-981, 45, -1], ![-2518, 66, 0]], ![![222, 21, -1], ![570, 65, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {100} * I131N1 =  Ideal.span {B.equivFun.symm ![-93, 11, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E131RS1 


noncomputable def E131RS2 : RelationCertificate Table 2 ![![131, 0, 0], ![-4, 1, 0]]
  ![47, 15, 3] ![![2, 0, 0], ![-22, -2, 1]] where
    su := ![![262, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![94, 30, 6], ![352, 122, 26]]
    hw := by decide
    g := ![![![69329, -40780, 138062], ![-652687, -94140, 0]], ![![-1908, 1135, -3836], ![18132, 2615, 0]]]
    h := ![![![57, -12, -1], ![1855, 67, 0]], ![![192, -45, -1], ![6244, 72, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {2} * I131N2 =  Ideal.span {B.equivFun.symm ![47, 15, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E131RS2 


noncomputable def E137RS1 : RelationCertificate Table 25 ![![137, 0, 0], ![30, 1, 0]]
  ![-313, -49, 16] ![![25, 0, 0], ![3, 1, 0]] where
    su := ![![3425, 0, 0], ![750, 25, 0]]
    hsu := by decide
    w := ![![-7825, -1225, 400], ![1525, 100, -50]]
    hw := by decide
    g := ![![![20311, -4287879, -2863098], ![-169076, 35788742, 0]], ![![4616, -974518, -650704], ![-38414, 8133805, 0]]]
    h := ![![![-2009, -99, -2], ![9164, 145, 0]], ![![353, 12, 0], ![-1610, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {25} * I137N1 =  Ideal.span {B.equivFun.symm ![-313, -49, 16]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E137RS1 
