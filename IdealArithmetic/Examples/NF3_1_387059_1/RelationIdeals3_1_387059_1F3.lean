import IdealArithmetic.Examples.NF3_1_387059_1.PrimesBelow3_1_387059_1F3
import IdealArithmetic.Examples.NF3_1_387059_1.ClassGroupData3_1_387059_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 128 ![![139, 0, 0], ![19, 1, 0]]
  ![-10, 67, 20] ![![128, 0, 0], ![-9, 1, 0]] where
    su := ![![17792, 0, 0], ![2432, 128, 0]]
    hsu := by decide
    w := ![![-1280, 8576, 2560], ![384, -1280, 128]]
    hw := by decide
    g := ![![![-76749719773, 386641978491, -154683094911], ![8417105168, 4949859036387, -399]], ![![-10964437365, 55235534040, -22097971327], ![1202464736, 707135082355, -57]]]
    h := ![![![71414, 660549, 146812], ![14572, -5101712, 0]], ![![-18914, -174919, -38877], ![-3837, 1350976, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {128} * I139N1 =  Ideal.span {B.equivFun.symm ![-10, 67, 20]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 64 ![![149, 0, 0], ![-68, 1, 0]]
  ![94, -9, 4] ![![64, 0, 0], ![-9, 1, 0]] where
    su := ![![9536, 0, 0], ![-4352, 64, 0]]
    hsu := by decide
    w := ![![6016, -576, 256], ![-832, 64, -64]]
    hw := by decide
    g := ![![![-3009165191880, 15503288174825, -6205469926506], ![665402732858, 99287543054438, 13845909]], ![![1342933077087, -6918822053950, 2769382965631], ![-296956558554, -44310138263637, -6179166]]]
    h := ![![![2682, -124393, 7212], ![-2026, -268646, 0]], ![![-353, 17196, -997], ![319, 37138, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {64} * I149N1 =  Ideal.span {B.equivFun.symm ![94, -9, 4]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E149RS1 


noncomputable def E151RS0 : RelationCertificate Table 512 ![![151, 0, 0], ![30, 1, 0]]
  ![442, 21, 12] ![![512, 0, 0], ![119, 1, 0]] where
    su := ![![77312, 0, 0], ![15360, 512, 0]]
    hsu := by decide
    w := ![![226304, 10752, 6144], ![52736, 2560, 1536]]
    hw := by decide
    g := ![![![394178, 25193013, 853970], ![141228, -109313211, 167]], ![![84855, 5428252, 184002], ![30762, -23553345, 36]]]
    h := ![![![24974, 384025, 52976], ![7635, -1999841, 0]], ![![5809, 89489, 12345], ![1833, -466023, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N0 : Ideal.span {512} * I151N0 =  Ideal.span {B.equivFun.symm ![442, 21, 12]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E151RS0 


noncomputable def E151RS1 : RelationCertificate Table 256 ![![151, 0, 0], ![43, 1, 0]]
  ![-1698, 23, -60] ![![256, 0, 0], ![119, 1, 0]] where
    su := ![![38656, 0, 0], ![11008, 256, 0]]
    hsu := by decide
    w := ![![-434688, 5888, -15360], ![-202496, 2816, -7168]]
    hw := by decide
    g := ![![![19106589456, 1535293939119, 52045832562], ![14878820699, -3330933281673, -76]], ![![6035090818, 484944655814, 16439424214], ![4699689485, -1052123148971, -24]]]
    h := ![![![-111046216, -2624698773, -250002220], ![-49004434, 9437583790, 0]], ![![-51730157, -1222698431, -116461868], ![-22828328, 4396435510, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {256} * I151N1 =  Ideal.span {B.equivFun.symm ![-1698, 23, -60]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E151RS1 


noncomputable def E151RS2 : RelationCertificate Table 32 ![![151, 0, 0], ![-74, 1, 0]]
  ![-2, 23, 4] ![![32, 0, 0], ![-9, 1, 0]] where
    su := ![![4832, 0, 0], ![-2368, 32, 0]]
    hsu := by decide
    w := ![![-64, 736, 128], ![96, -352, 64]]
    hw := by decide
    g := ![![![12813665698837, -72122635335706, 28922279970708], ![-5857675832019, -231378225357363, 8233302]], ![![-6256437718335, 35214807898516, -14121676619481], ![2860085855118, 112973405920809, -4020016]]]
    h := ![![![0, 1800, -96], ![98, 3625, 0]], ![![113, -2363, 126], ![102, -4756, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N2 : Ideal.span {32} * I151N2 =  Ideal.span {B.equivFun.symm ![-2, 23, 4]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E151RS2 


noncomputable def E157RS1 : RelationCertificate Table 2 ![![157, 0, 0], ![-58, 1, 0]]
  ![0, -3, -2] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![314, 0, 0], ![-116, 2, 0]]
    hsu := by decide
    w := ![![0, -6, -4], ![-22, 60, -18]]
    hw := by decide
    g := ![![![0, 693, -114], ![1726, 0, 105]], ![![0, -281, 44], ![-624, 0, -40]]]
    h := ![![![16, 29, -2], ![46, 78, 0]], ![![183, -5237, 355], ![15, -13936, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {2} * I157N1 =  Ideal.span {B.equivFun.symm ![0, -3, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 512 ![![163, 0, 0], ![-5, 1, 0]]
  ![10258, -159, 348] ![![512, 0, 0], ![119, 1, 0]] where
    su := ![![83456, 0, 0], ![-2560, 512, 0]]
    hsu := by decide
    w := ![![5252096, -81408, 178176], ![1223168, -18944, 41472]]
    hw := by decide
    g := ![![![3132168685701, 200138997026360, 6784413525544], ![1118880997746, -868409162392702, 139871837]], ![![-82228772295, -5254245746129, -178111094970], ![-29373963698, 22798331235764, -3672053]]]
    h := ![![![-48960, 147281, -98196], ![2482, 4001574, 0]], ![![-11400, 34300, -22869], ![655, 931932, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {512} * I163N1 =  Ideal.span {B.equivFun.symm ![10258, -159, 348]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E163RS1 


noncomputable def E167RS0 : RelationCertificate Table 128 ![![167, 0, 0], ![81, 1, 0]]
  ![-66, 7, 4] ![![128, 0, 0], ![-9, 1, 0]] where
    su := ![![21376, 0, 0], ![10368, 128, 0]]
    hsu := by decide
    w := ![![-8448, 896, 512], ![640, -256, 0]]
    hw := by decide
    g := ![![![-25744199352, 129691524677, -51885432790], ![2823354073, 1660333850013, 420]], ![![-12503279324, 62987756459, -25199387643], ![1371228687, 806380404932, 204]]]
    h := ![![![-279, -12560, -628], ![-73, 26220, 0]], ![![-56, 959, 48], ![165, -2004, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N0 : Ideal.span {128} * I167N0 =  Ideal.span {B.equivFun.symm ![-66, 7, 4]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E167RS0 


noncomputable def E167RS1 : RelationCertificate Table 2 ![![167, 0, 0], ![-51, 1, 0]]
  ![-62, 1, -2] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![334, 0, 0], ![-102, 2, 0]]
    hsu := by decide
    w := ![![-124, 2, -4], ![-76, -2, -2]]
    hw := by decide
    g := ![![![-975, 2197, -249], ![611, 0, 167]], ![![297, -672, 76], ![-185, 0, -51]]]
    h := ![![![1553, -45886, 3530], ![-693, -147378, 0]], ![![974, -28091, 2161], ![-348, -90222, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {2} * I167N1 =  Ideal.span {B.equivFun.symm ![-62, 1, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E167RS1 


noncomputable def E167RS2 : RelationCertificate Table 8 ![![167, 0, 0], ![-31, 1, 0]]
  ![358, -5, 12] ![![8, 0, 0], ![-1, 1, 0]] where
    su := ![![1336, 0, 0], ![-248, 8, 0]]
    hsu := by decide
    w := ![![2864, -40, 96], ![-272, 8, -8]]
    hw := by decide
    g := ![![![17108059781, -17113343453, 35281935907], ![-4277675399, -70563391482, -1921335]], ![![-3176015331, 3176996215, -6549893489], ![794126447, 13099697807, 356685]]]
    h := ![![![361696, -6094227, 761856], ![-103616, -31807485, 0]], ![![-34358, 578909, -72371], ![9846, 3021489, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N2 : Ideal.span {8} * I167N2 =  Ideal.span {B.equivFun.symm ![358, -5, 12]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E167RS2 


noncomputable def E173RS1 : RelationCertificate Table 16 ![![173, 0, 0], ![-41, 1, 0]]
  ![6, -21, 4] ![![16, 0, 0], ![7, 1, 0]] where
    su := ![![2768, 0, 0], ![-656, 16, 0]]
    hsu := by decide
    w := ![![96, -336, 64], ![32, -240, -48]]
    hw := by decide
    g := ![![![-4678786919, -17349524834, -12019569026], ![-3131314569, 47677623773, 178067689]], ![![1108847081, 4111743140, 2848572567], ![742104549, -11299337842, -42201075]]]
    h := ![![![502, -11297, 1076], ![-152, -46536, 0]], ![![194, -3875, 369], ![40, -15960, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {16} * I173N1 =  Ideal.span {B.equivFun.symm ![6, -21, 4]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E173RS1 
