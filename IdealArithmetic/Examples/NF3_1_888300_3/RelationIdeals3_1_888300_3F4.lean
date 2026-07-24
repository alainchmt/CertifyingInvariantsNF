import IdealArithmetic.Examples.NF3_1_888300_3.PrimesBelow3_1_888300_3F4
import IdealArithmetic.Examples.NF3_1_888300_3.ClassGroupData3_1_888300_3

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 147 ![![197, 0, 0], ![33, 1, 0]]
  ![-1019, -71, 10] ![![147, 0, 0], ![-114, -1, 1]] where
    su := ![![28959, 0, 0], ![4851, 147, 0]]
    hsu := by decide
    w := ![![-149793, -10437, 1470], ![57036, 4263, -588]]
    hw := by decide
    g := ![![![-53757, -3969, -167], ![41908, 17370, 0]], ![![-9225, -683, -29], ![7251, 2990, 0]]]
    h := ![![![-1027, -33, 0], ![6100, 10, 0]], ![![338, -22, -1], ![-2006, 193, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {147} * I197N1 =  Ideal.span {B.equivFun.symm ![-1019, -71, 10]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E197RS1 


noncomputable def E211RS1 : RelationCertificate Table 7 ![![211, 0, 0], ![-4, 1, 0]]
  ![-79, -25, -2] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![1477, 0, 0], ![-28, 7, 0]]
    hsu := by decide
    w := ![![-553, -175, -14], ![-1302, -329, -21]]
    hw := by decide
    g := ![![![-251, 11, -18], ![78, 145, 0]], ![![14, 1, 0], ![-2, -1, 0]]]
    h := ![![![-81, 24, -1], ![-4253, 209, 0]], ![![-190, 51, -1], ![-9976, 208, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {7} * I211N1 =  Ideal.span {B.equivFun.symm ![-79, -25, -2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E211RS1 


noncomputable def E227RS1 : RelationCertificate Table 21 ![![227, 0, 0], ![71, 1, 0]]
  ![701, 50, -7] ![![21, 0, 0], ![-93, -1, 1]] where
    su := ![![4767, 0, 0], ![1491, 21, 0]]
    hsu := by decide
    w := ![![14721, 1050, -147], ![-23583, -1911, 252]]
    hw := by decide
    g := ![![![23505, 33204, 4339], ![-105174, -14074, 0]], ![![7258, 10240, 1338], ![-32431, -4340, 0]]]
    h := ![![![3311, 49, 0], ![-10576, -7, 0]], ![![-5461, -152, -1], ![17444, 239, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {21} * I227N1 =  Ideal.span {B.equivFun.symm ![701, 50, -7]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E227RS1 


noncomputable def E229RS0 : RelationCertificate Table 7 ![![229, 0, 0], ![14, 1, 0]]
  ![-271, -73, -5] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![1603, 0, 0], ![98, 7, 0]]
    hsu := by decide
    w := ![![-1897, -511, -35], ![-3108, -875, -63]]
    hw := by decide
    g := ![![![449, 176, -70], ![-97, 458, 0]], ![![14, 9, -4], ![-2, 27, 0]]]
    h := ![![![-23311, -1679, -1], ![381282, 224, 0]], ![![-38152, -2739, -1], ![624026, 220, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N0 : Ideal.span {7} * I229N0 =  Ideal.span {B.equivFun.symm ![-271, -73, -5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E229RS0 


noncomputable def E229RS1 : RelationCertificate Table 49 ![![229, 0, 0], ![64, 1, 0]]
  ![369, 3, -2] ![![49, 0, 0], ![-23, 1, 0]] where
    su := ![![11221, 0, 0], ![3136, 49, 0]]
    hsu := by decide
    w := ![![18081, 147, -98], ![-9947, 0, 49]]
    hw := by decide
    g := ![![![-3348011, -426509377, 18550215], ![-7132726, -908960532, 0]], ![![-928377, -118267886, 5143837], ![-1977849, -252048012, 0]]]
    h := ![![![5917, 93, 0], ![-21166, -2, 0]], ![![-3311, -116, -1], ![11844, 230, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {49} * I229N1 =  Ideal.span {B.equivFun.symm ![369, 3, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E229RS1 


noncomputable def E239RS1 : RelationCertificate Table 49 ![![239, 0, 0], ![-74, 1, 0]]
  ![12279, 3390, 239] ![![49, 0, 0], ![-23, 1, 0]] where
    su := ![![11711, 0, 0], ![-3626, 49, 0]]
    hsu := by decide
    w := ![![601671, 166110, 11711], ![-107947, -29841, -2107]]
    hw := by decide
    g := ![![![15467843, 1970418440, -85699609], ![32952226, 4199280622, 0]], ![![-4717723, -600980318, 26138498], ![-10050461, -1280786328, 0]]]
    h := ![![![234053, -3296, 3], ![755762, -478, 0]], ![![-41957, 625, -1], ![-135480, 196, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {49} * I239N1 =  Ideal.span {B.equivFun.symm ![12279, 3390, 239]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E239RS1 


noncomputable def E257RS1 : RelationCertificate Table 147 ![![257, 0, 0], ![62, 1, 0]]
  ![4019, 1108, 78] ![![147, 0, 0], ![-644, -35, 7]] where
    su := ![![37779, 0, 0], ![9114, 147, 0]]
    hsu := by decide
    w := ![![590793, 162876, 11466], ![1080744, 298263, 21021]]
    hw := by decide
    g := ![![![8685, 4975, 630], ![-38939, -5187, 0]], ![![2130, 1205, 152], ![-9414, -1254, 0]]]
    h := ![![![21813879, 384248, 523], ![-90421982, -134333, 0]], ![![39904444, 702989, 958], ![-165410238, -246063, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N1 : Ideal.span {147} * I257N1 =  Ideal.span {B.equivFun.symm ![4019, 1108, 78]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E257RS1 
