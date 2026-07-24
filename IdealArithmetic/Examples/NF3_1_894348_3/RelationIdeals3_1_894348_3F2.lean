import IdealArithmetic.Examples.NF3_1_894348_3.PrimesBelow3_1_894348_3F2
import IdealArithmetic.Examples.NF3_1_894348_3.ClassGroupData3_1_894348_3

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 275 ![![89, 0, 0], ![13, 1, 0]]
  ![-743217, -68558, -44269] ![![275, 0, 0], ![51, 1, 0]] where
    su := ![![24475, 0, 0], ![3575, 275, 0]]
    hsu := by decide
    w := ![![-204384675, -18853450, -12173975], ![-45961025, -4239675, -2737625]]
    hw := by decide
    g := ![![![11789764, -18083751697, -2482115295], ![-63572441, 97511672344, 0]], ![![1769923, -2714809494, -372625674], ![-9543718, 14638865775, 0]]]
    h := ![![![-2244200351, -176867694, -2281835], ![15364083694, 29005578, 0]], ![![-504664789, -39773147, -513131], ![3454999930, 6522672, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {275} * I89N1 =  Ideal.span {B.equivFun.symm ![-743217, -68558, -44269]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 11 ![![101, 0, 0], ![41, 1, 0]]
  ![-571, -96, 96] ![![11, 0, 0], ![-4, 1, 0]] where
    su := ![![1111, 0, 0], ![451, 11, 0]]
    hsu := by decide
    w := ![![-6281, -1056, 1056], ![19756, -187, -1056]]
    hw := by decide
    g := ![![![106133, 3134115, -5520232], ![246335, 8676200, 0]], ![![45149, 1289163, -2270192], ![100790, 3568240, 0]]]
    h := ![![![-131366, -4089, -150], ![323595, 2178, 0]], ![![412028, 12737, 458], ![-1014952, -6622, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {11} * I101N1 =  Ideal.span {B.equivFun.symm ![-571, -96, 96]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 275 ![![107, 0, 0], ![52, 1, 0]]
  ![-3483, 408, -56] ![![275, 0, 0], ![51, 1, 0]] where
    su := ![![29425, 0, 0], ![14300, 275, 0]]
    hsu := by decide
    w := ![![-957825, 112200, -15400], ![-187825, 17325, 0]]
    hw := by decide
    g := ![![![-7979298, 12238634054, 1679833981], ![43024465, -65993478329, 0]], ![![-3872517, 5939577404, 815246530], ![20880537, -32027542546, 0]]]
    h := ![![![-44061, -1099, -35], ![90597, 527, 0]], ![![-8669, -218, -7], ![17825, 107, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {275} * I107N1 =  Ideal.span {B.equivFun.symm ![-3483, 408, -56]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 25 ![![109, 0, 0], ![31, 1, 0]]
  ![-951, 176, -57] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![2725, 0, 0], ![775, 25, 0]]
    hsu := by decide
    w := ![![-23775, 4400, -1425], ![-11325, -775, 1175]]
    hw := by decide
    g := ![![![4359, 1380, 7165], ![234, -24660, 0]], ![![1673, 435, 2089], ![96, -7104, 0]]]
    h := ![![![-372507, -13788, -401], ![1309752, 6236, 0]], ![![-177885, -6595, -193], ![625452, 3012, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {25} * I109N0 =  Ideal.span {B.equivFun.symm ![-951, 176, -57]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 25 ![![109, 0, 0], ![-22, 1, 0]]
  ![369, 31, -42] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![2725, 0, 0], ![-550, 25, 0]]
    hsu := by decide
    w := ![![9225, 775, -1050], ![-7275, 400, 175]]
    hw := by decide
    g := ![![![-700, 64928, 455567], ![2575, -1627152, 0]], ![![82, -13135, -92127], ![-522, 329038, 0]]]
    h := ![![![555, -4, -7], ![2733, 103, 0]], ![![-369, 39, -7], ![-1815, 110, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {25} * I109N1 =  Ideal.span {B.equivFun.symm ![369, 31, -42]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 25 ![![109, 0, 0], ![-9, 1, 0]]
  ![-137, -13, -9] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![2725, 0, 0], ![-225, 25, 0]]
    hsu := by decide
    w := ![![-3425, -325, -225], ![-1775, -150, -100]]
    hw := by decide
    g := ![![![5, -755, -5288], ![-24, 18886, 0]], ![![-1, 55, 390], ![20, -1393, 0]]]
    h := ![![![-31232, 3493, -18], ![-378239, 279, 0]], ![![-16190, 1818, -15], ![-196071, 233, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {25} * I109N2 =  Ideal.span {B.equivFun.symm ![-137, -13, -9]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E109RS2 


noncomputable def E113RS1 : RelationCertificate Table 3025 ![![113, 0, 0], ![-25, 1, 0]]
  ![1403, -103, -29] ![![3025, 0, 0], ![601, 1, 0]] where
    su := ![![341825, 0, 0], ![-75625, 3025, 0]]
    hsu := by decide
    w := ![![4244075, -311575, -87725], ![837925, -60500, -18150]]
    hw := by decide
    g := ![![![-895, 11147090, 129833], ![4504, -56106409, 0]], ![![-88, -2033956, -23690], ![443, 10237465, 0]]]
    h := ![![![109692531, -4584999, 55243], ![495810184, -891784, 0]], ![![21656979, -905233, 10907], ![97889534, -176071, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {3025} * I113N1 =  Ideal.span {B.equivFun.symm ![1403, -103, -29]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E113RS1 


noncomputable def E127RS0 : RelationCertificate Table 55 ![![127, 0, 0], ![33, 1, 0]]
  ![9851, 909, 587] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![6985, 0, 0], ![1815, 55, 0]]
    hsu := by decide
    w := ![![541805, 49995, 32285], ![67430, 6215, 4015]]
    hw := by decide
    g := ![![![-25, -1951, 3418], ![-26, -26852, 0]], ![![-3, -510, 892], ![32, -7007, 0]]]
    h := ![![![12518738, 413258, 7195], ![-48177875, -130454, 0]], ![![1557962, 51414, 892], ![-5995756, -16173, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {55} * I127N0 =  Ideal.span {B.equivFun.symm ![9851, 909, 587]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 55 ![![127, 0, 0], ![-25, 1, 0]]
  ![953, 87, 56] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![6985, 0, 0], ![-1375, 55, 0]]
    hsu := by decide
    w := ![![52415, 4785, 3080], ![6380, 605, 385]]
    hw := by decide
    g := ![![![-242171, -184116580, 322309967], ![-3329949, -2532435456, 0]], ![![46475, 35331837, -61851048], ![639053, 485972520, 0]]]
    h := ![![![13714, -546, 0], ![69629, 8, 0]], ![![1708, -68, 0], ![8672, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {55} * I127N1 =  Ideal.span {B.equivFun.symm ![953, 87, 56]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 55 ![![127, 0, 0], ![-8, 1, 0]]
  ![-1663, 93, 39] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![6985, 0, 0], ![-440, 55, 0]]
    hsu := by decide
    w := ![![-91465, 5115, 2145], ![13750, -2035, 495]]
    hw := by decide
    g := ![![![-102823, -77646115, 135925228], ![-1404246, -1067984260, 0]], ![![5900, 4496766, -7871932], ![81339, 61850887, 0]]]
    h := ![![![-1857, 235, -3], ![-29272, 60, 0]], ![![294, -31, -5], ![4636, 92, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {55} * I127N2 =  Ideal.span {B.equivFun.symm ![-1663, 93, 39]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E127RS2 


noncomputable def E131RS1 : RelationCertificate Table 5 ![![131, 0, 0], ![25, 1, 0]]
  ![4651, 429, 277] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![655, 0, 0], ![125, 5, 0]]
    hsu := by decide
    w := ![![23255, 2145, 1385], ![55065, 5080, 3280]]
    hw := by decide
    g := ![![![161, 3, 158], ![34, -114, 0]], ![![28, 3, 41], ![9, -30, 0]]]
    h := ![![![17546, 714, 5], ![-91755, -54, 0]], ![![41598, 1729, 22], ![-217533, -318, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {5} * I131N1 =  Ideal.span {B.equivFun.symm ![4651, 429, 277]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 605 ![![137, 0, 0], ![-10, 1, 0]]
  ![557, -12, -21] ![![605, 0, 0], ![-4, 1, 0]] where
    su := ![![82885, 0, 0], ![-6050, 605, 0]]
    hsu := by decide
    w := ![![336985, -7260, -12705], ![-6050, 605, 0]]
    hw := by decide
    g := ![![![1, 7524, -13167], ![42, 1138008, 0]], ![![0, -480, 840], ![1, -72600, 0]]]
    h := ![![![3514641, -353244, 1246], ![48150526, -24389, 0]], ![![-63090, 6349, -28], ![-864332, 548, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {605} * I137N1 =  Ideal.span {B.equivFun.symm ![557, -12, -21]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E137RS1 
