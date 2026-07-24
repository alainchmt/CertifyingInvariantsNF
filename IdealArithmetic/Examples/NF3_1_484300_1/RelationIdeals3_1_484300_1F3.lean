import IdealArithmetic.Examples.NF3_1_484300_1.PrimesBelow3_1_484300_1F3
import IdealArithmetic.Examples.NF3_1_484300_1.ClassGroupData3_1_484300_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 9 ![![139, 0, 0], ![44, 1, 0]]
  ![-195824, 15005, -7680] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![1251, 0, 0], ![396, 9, 0]]
    hsu := by decide
    w := ![![-1762416, 135045, -69120], ![168669, -12924, 6615]]
    hw := by decide
    g := ![![![-2468262, -14354612, -10990107], ![-2691955, 32970446, -114]], ![![-844395, -4910783, -3759771], ![-920925, 11279358, -39]]]
    h := ![![![363144, 19605300, 1336788], ![256081, -61940404, 0]], ![![-34773, -1876292, -127935], ![-24448, 5927900, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {9} * I139N1 =  Ideal.span {B.equivFun.symm ![-195824, 15005, -7680]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 3 ![![149, 0, 0], ![23, 1, 0]]
  ![586, 209, 57] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![447, 0, 0], ![69, 3, 0]]
    hsu := by decide
    w := ![![1758, 627, 171], ![-6159, -117, 741]]
    hw := by decide
    g := ![![![957023, -56512, 8122], ![300173, 0, 14740]], ![![197705, -4317, -495], ![64464, 0, 4020]]]
    h := ![![![693, 17154, 2238], ![368, -111135, 0]], ![![-2590, -61702, -8047], ![-691, 399750, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {3} * I149N1 =  Ideal.span {B.equivFun.symm ![586, 209, 57]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E149RS1 


noncomputable def E151RS1 : RelationCertificate Table 9 ![![151, 0, 0], ![-47, 1, 0]]
  ![282415, -21640, 11076] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![1359, 0, 0], ![-423, 9, 0]]
    hsu := by decide
    w := ![![2541735, -194760, 99684], ![-243252, 18639, -9540]]
    hw := by decide
    g := ![![![12408545, 72177625, 55260598], ![13534647, -165782296, 302]], ![![-3903354, -22704885, -17383302], ![-4257584, 52150059, -95]]]
    h := ![![![12252959, -699286242, 44638926], ![-8444848, -2246822250, 0]], ![![-1172642, 66923883, -4272085], ![808213, 215027925, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {9} * I151N1 =  Ideal.span {B.equivFun.symm ![282415, -21640, 11076]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 9 ![![157, 0, 0], ![67, 1, 0]]
  ![-5585, 428, -219] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![1413, 0, 0], ![603, 9, 0]]
    hsu := by decide
    w := ![![-50265, 3852, -1971], ![4806, -369, 189]]
    hw := by decide
    g := ![![![-26870, -150482, -115077], ![-28656, 345373, -87]], ![![-12044, -67457, -51586], ![-12844, 154821, -39]]]
    h := ![![![108970, 10556633, 472716], ![113806, -24738877, 0]], ![![-10423, -1009356, -45198], ![-10872, 2365369, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {9} * I157N1 =  Ideal.span {B.equivFun.symm ![-5585, 428, -219]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E157RS1 


noncomputable def E179RS0 : RelationCertificate Table 3 ![![179, 0, 0], ![15, 1, 0]]
  ![458, -35, 18] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![537, 0, 0], ![45, 3, 0]]
    hsu := by decide
    w := ![![1374, -105, 54], ![-1773, 135, -69]]
    hw := by decide
    g := ![![![104456, 3291, -1911], ![35918, 0, 2864]], ![![8462, 266, -155], ![2911, 0, 232]]]
    h := ![![![1822, 27807, 5562], ![412, -331860, 0]], ![![-2364, -35882, -7177], ![-377, 428220, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N0 : Ideal.span {3} * I179N0 =  Ideal.span {B.equivFun.symm ![458, -35, 18]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E179RS0 


noncomputable def E179RS1 : RelationCertificate Table 3 ![![179, 0, 0], ![72, 1, 0]]
  ![-7855991, 601964, -308103] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![537, 0, 0], ![216, 3, 0]]
    hsu := by decide
    w := ![![-23567973, 1805892, -924309], ![30334539, -2324379, 1189686]]
    hw := by decide
    g := ![![![-19118, -1109, 209], ![-6739, 0, -358]], ![![-7639, -478, 59], ![-2705, 0, -143]]]
    h := ![![![26202347, 2618481933, 109107411], ![25168085, -6510178224, 0]], ![![-33725380, -3370270424, -140433079], ![-32393769, 8379305901, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {3} * I179N1 =  Ideal.span {B.equivFun.symm ![-7855991, 601964, -308103]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E179RS1 


noncomputable def E179RS2 : RelationCertificate Table 3 ![![179, 0, 0], ![-88, 1, 0]]
  ![1147, -88, 45] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![537, 0, 0], ![-264, 3, 0]]
    hsu := by decide
    w := ![![3441, -264, 135], ![-4431, 339, -174]]
    hw := by decide
    g := ![![![10338, 333, -183], ![3559, 0, 284]], ![![-5028, -163, 89], ![-1728, 0, -138]]]
    h := ![![![17465, -2505140, 85407], ![-22396, -5095936, 0]], ![![-22342, 3225879, -109979], ![29140, 6562061, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N2 : Ideal.span {3} * I179N2 =  Ideal.span {B.equivFun.symm ![1147, -88, 45]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E179RS2 


noncomputable def E191RS1 : RelationCertificate Table 3 ![![191, 0, 0], ![-38, 1, 0]]
  ![-28685, 2198, -1125] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![573, 0, 0], ![-114, 3, 0]]
    hsu := by decide
    w := ![![-86055, 6594, -3375], ![110763, -8487, 4344]]
    hw := by decide
    g := ![![![-111162, -3521, 2011], ![-38225, 0, -3056]], ![![22422, 711, -405], ![7714, 0, 616]]]
    h := ![![![28063, -1158813, 91485], ![-11479, -5824920, 0]], ![![-36075, 1491528, -117752], ![15003, 7497360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {3} * I191N1 =  Ideal.span {B.equivFun.symm ![-28685, 2198, -1125]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 9 ![![193, 0, 0], ![-17, 1, 0]]
  ![5031763, -385558, 197340] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![1737, 0, 0], ![-153, 9, 0]]
    hsu := by decide
    w := ![![45285867, -3470022, 1776060], ![-4333986, 332091, -169974]]
    hw := by decide
    g := ![![![4400916573037003, 25605332658459699, 19604082813642856], ![4800999883400867, -58812248444297792, 2021480]], ![![-385647328562745, -2243766263872021, -1717883545514978], ![-420706175346994, 5153650636840192, -177140]]]
    h := ![![![-46335491, 800423840, -141258120], ![8228822, 9087671500, 0]], ![![4434451, -76602834, 13518803], ![-787374, -869715955, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {9} * I193N1 =  Ideal.span {B.equivFun.symm ![5031763, -385558, 197340]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E193RS1 


noncomputable def E193RS2 : RelationCertificate Table 3 ![![193, 0, 0], ![-10, 1, 0]]
  ![-10, 1, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![579, 0, 0], ![-30, 3, 0]]
    hsu := by decide
    w := ![![-30, 3, 0], ![-9, -9, 3]]
    hw := by decide
    g := ![![![-14097, -444, 257], ![-4847, 0, -386]], ![![767, 24, -14], ![264, 0, 21]]]
    h := ![![![28, -280, 84], ![1, -5404, 0]], ![![15, -84, 25], ![129, -1608, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N2 : Ideal.span {3} * I193N2 =  Ideal.span {B.equivFun.symm ![-10, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E193RS2 
