import IdealArithmetic.Examples.NF3_3_895700_1.PrimesBelow3_3_895700_1F3
import IdealArithmetic.Examples.NF3_3_895700_1.ClassGroupData3_3_895700_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 9 ![![139, 0, 0], ![-66, 1, 0]]
  ![-23, 0, 1] ![![9, 0, 0], ![-1, 1, 0]] where
    su := ![![1251, 0, 0], ![-594, 9, 0]]
    hsu := by decide
    w := ![![-207, 0, 9], ![-405, 63, 0]]
    hw := by decide
    g := ![![![-1194843, 1194794, -2448587], ![265518, 11018645, 0]], ![![563857, -563836, 1155513], ![-125294, -5199810, 0]]]
    h := ![![![5001, -520663, 15779], ![-6083, -1096640, 0]], ![![9823, -1022650, 30992], ![-11947, -2153944, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {9} * I139N1 =  Ideal.span {B.equivFun.symm ![-23, 0, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E139RS1 


noncomputable def E151RS1 : RelationCertificate Table 3249 ![![151, 0, 0], ![-41, 1, 0]]
  ![-11890, 513, 182] ![![3249, 0, 0], ![-685, 1, 0]] where
    su := ![![490599, 0, 0], ![-133209, 3249, 0]]
    hsu := by decide
    w := ![![-38630610, 1666737, 591318], ![8067267, -347643, -123462]]
    hw := by decide
    g := ![![![147131913083, -110162172829314, 321641438870], ![-64926907792, -522506517444305, 0]], ![![-39035592440, 29227144707876, -85334744554], ![17225770351, 138626292527970, 0]]]
    h := ![![![143089, -6802096, 331838], ![-83789, -25053678, 0]], ![![-29871, 1420487, -69298], ![17536, 5231980, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {3249} * I151N1 =  Ideal.span {B.equivFun.symm ![-11890, 513, 182]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 57 ![![157, 0, 0], ![57, 1, 0]]
  ![59, 0, -4] ![![57, 0, 0], ![-1, 1, 0]] where
    su := ![![8949, 0, 0], ![3249, 57, 0]]
    hsu := by decide
    w := ![![3363, 0, -228], ![1653, -285, 0]]
    hw := by decide
    g := ![![![54, -79, 160], ![1, -4550, 0]], ![![22, -32, 64], ![23, -1820, 0]]]
    h := ![![![-1288, -93815, -3292], ![-985, 258420, 0]], ![![-637, -46167, -1620], ![-476, 127170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {57} * I157N1 =  Ideal.span {B.equivFun.symm ![59, 0, -4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E157RS1 


noncomputable def E167RS1 : RelationCertificate Table 171 ![![167, 0, 0], ![-62, 1, 0]]
  ![-175, 0, 8] ![![171, 0, 0], ![-1, 1, 0]] where
    su := ![![28557, 0, 0], ![-10602, 171, 0]]
    hsu := by decide
    w := ![![-29925, 0, 1368], ![-3249, 513, 0]]
    hw := by decide
    g := ![![![-205024994, 205024985, -410078016], ![2398009, 35061670380, 0]], ![![212392179, -212392176, 424813404], ![-2483971, -36321546046, 0]]]
    h := ![![![918, -70489, 2274], ![-587, -189875, 0]], ![![125, -7688, 248], ![3, -20708, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {171} * I167N1 =  Ideal.span {B.equivFun.symm ![-175, 0, 8]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 19 ![![173, 0, 0], ![-76, 1, 0]]
  ![192, -19, -4] ![![19, 0, 0], ![-1, 1, 0]] where
    su := ![![3287, 0, 0], ![-1444, 19, 0]]
    hsu := by decide
    w := ![![3648, -361, -76], ![1501, -133, -38]]
    hw := by decide
    g := ![![![1236, -1199, 2406], ![-110, -22862, 0]], ![![-538, 523, -1052], ![71, 9996, 0]]]
    h := ![![![-159756, 17951257, -472428], ![174040, 40865020, 0]], ![![-65673, 7385037, -194354], ![71712, 16811620, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {19} * I173N1 =  Ideal.span {B.equivFun.symm ![192, -19, -4]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E173RS1 


noncomputable def E179RS1 : RelationCertificate Table 171 ![![179, 0, 0], ![54, 1, 0]]
  ![-89, 0, 7] ![![171, 0, 0], ![-1, 1, 0]] where
    su := ![![30609, 0, 0], ![9234, 171, 0]]
    hsu := by decide
    w := ![![-15219, 0, 1197], ![-2907, 513, 0]]
    hw := by decide
    g := ![![![301750734, -301750725, 603542727], ![-3529243, -51602903169, 0]], ![![90442583, -90442580, 180897531], ![-1057740, -15466738904, 0]]]
    h := ![![![521, 33828, 1253], ![348, -112140, 0]], ![![65, 6479, 240], ![182, -21480, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {171} * I179N1 =  Ideal.span {B.equivFun.symm ![-89, 0, 7]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E179RS1 


noncomputable def E181RS1 : RelationCertificate Table 57 ![![181, 0, 0], ![-34, 1, 0]]
  ![1153, -114, -26] ![![57, 0, 0], ![-1, 1, 0]] where
    su := ![![10317, 0, 0], ![-1938, 57, 0]]
    hsu := by decide
    w := ![![65721, -6498, -1482], ![9861, -969, -228]]
    hw := by decide
    g := ![![![-7031546, 7031565, -14071790], ![246753, 401046008, 0]], ![![752643, -752646, 1506218], ![-26381, -42927212, 0]]]
    h := ![![![9807, -357560, 21034], ![-3814, -1903590, 0]], ![![1495, -53650, 3156], ![-447, -285620, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {57} * I181N1 =  Ideal.span {B.equivFun.symm ![1153, -114, -26]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 9 ![![191, 0, 0], ![87, 1, 0]]
  ![-100, 9, 2] ![![9, 0, 0], ![-1, 1, 0]] where
    su := ![![1719, 0, 0], ![783, 9, 0]]
    hsu := by decide
    w := ![![-900, 81, 18], ![-747, 63, 18]]
    hw := by decide
    g := ![![![-1717763, 1717730, -3520284], ![381725, 15841280, 0]], ![![-783395, 783379, -1605442], ![174086, 7224490, 0]]]
    h := ![![![1422, 188781, 4340], ![1641, -414469, 0]], ![![1141, 156679, 3602], ![1448, -343990, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {9} * I191N1 =  Ideal.span {B.equivFun.symm ![-100, 9, 2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 361 ![![193, 0, 0], ![-90, 1, 0]]
  ![-10801, 380, 151] ![![361, 0, 0], ![37, 1, 0]] where
    su := ![![69673, 0, 0], ![-32490, 361, 0]]
    hsu := by decide
    w := ![![-3899161, 137180, 54511], ![-463885, 16245, 6498]]
    hw := by decide
    g := ![![![-716693703, -27080292300, -1463821815], ![-148470514, 264219837585, 0]], ![![316286679, 11950902912, 646004563], ![65522480, -116603823612, 0]]]
    h := ![![![37645848, -5270831567, 117134757], ![-44864939, -11303503975, 0]], ![![4478705, -627066510, 13935426], ![-5337525, -1344768600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {361} * I193N1 =  Ideal.span {B.equivFun.symm ![-10801, 380, 151]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E193RS1 
