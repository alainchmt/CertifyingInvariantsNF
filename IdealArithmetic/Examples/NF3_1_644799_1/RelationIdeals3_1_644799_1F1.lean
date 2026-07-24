import IdealArithmetic.Examples.NF3_1_644799_1.PrimesBelow3_1_644799_1F1
import IdealArithmetic.Examples.NF3_1_644799_1.ClassGroupData3_1_644799_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 25 ![![37, 0, 0], ![12, 1, 0]]
  ![43, 7, 3] ![![25, 0, 0], ![-12, 4, 1]] where
    su := ![![925, 0, 0], ![300, 25, 0]]
    hsu := by decide
    w := ![![1075, 175, 75], ![-3825, 0, 325]]
    hw := by decide
    g := ![![![-176, 11, -20], ![92, 0, 0]], ![![3, -2, -1], ![16, 0, 0]]]
    h := ![![![101515, -363981, -327021], ![23104, 1344420, 0]], ![![-362961, 1301325, 1169185], ![-82545, -4806648, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {25} * I37N0 =  Ideal.span {B.equivFun.symm ![43, 7, 3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E37RS0 


noncomputable def E41RS0 : RelationCertificate Table 3125 ![![41, 0, 0], ![20, 1, 0]]
  ![-17, -3, 3] ![![3125, 0, 0], ![-812, 1079, 1]] where
    su := ![![128125, 0, 0], ![62500, 3125, 0]]
    hsu := by decide
    w := ![![-53125, -9375, 9375], ![-481250, -6250, -21875]]
    hw := by decide
    g := ![![![20, -27, 0], ![78, 0, 0]], ![![811, -1078, -1], ![3122, 0, 0]]]
    h := ![![![-717, 4931, 2463], ![-214, -11220, 0]], ![![-6478, 44860, 22405], ![-2038, -102068, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {3125} * I41N0 =  Ideal.span {B.equivFun.symm ![-17, -3, 3]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 25 ![![41, 0, 0], ![-16, 1, 0]]
  ![11, -1, 1] ![![25, 0, 0], ![-12, 4, 1]] where
    su := ![![1025, 0, 0], ![-400, 25, 0]]
    hsu := by decide
    w := ![![275, -25, 25], ![-675, 50, -25]]
    hw := by decide
    g := ![![![-2, 1, 0], ![-8, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
    h := ![![![75, 446, -223], ![1, 1016, 0]], ![![-167, -1095, 547], ![41, -2492, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {25} * I41N1 =  Ideal.span {B.equivFun.symm ![11, -1, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 3125 ![![41, 0, 0], ![-5, 1, 0]]
  ![131, 15, 3] ![![3125, 0, 0], ![-812, 1079, 1]] where
    su := ![![128125, 0, 0], ![-15625, 3125, 0]]
    hsu := by decide
    w := ![![409375, 46875, 9375], ![-662500, 100000, 153125]]
    hw := by decide
    g := ![![![324, -440, -1], ![1277, 0, 0]], ![![191, -250, 0], ![723, 0, 0]]]
    h := ![![![-9607826, -22609886, 29050404], ![620238, -132340729, 0]], ![![16071955, 37821765, -48595447], ![-1037485, 221379264, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {3125} * I41N2 =  Ideal.span {B.equivFun.symm ![131, 15, 3]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E41RS2 


noncomputable def E43RS1 : RelationCertificate Table 125 ![![43, 0, 0], ![-9, 1, 0]]
  ![-34, 0, 3] ![![125, 0, 0], ![-62, -46, 1]] where
    su := ![![5375, 0, 0], ![-1125, 125, 0]]
    hsu := by decide
    w := ![![-4250, 0, 375], ![23375, 1375, -625]]
    hw := by decide
    g := ![![![56, 33, 0], ![93, 0, 0]], ![![35, 30, -1], ![80, 0, 0]]]
    h := ![![![-610, -2316, 1893], ![104, -9044, 0]], ![![3379, 12695, -10379], ![-406, 49588, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {125} * I43N1 =  Ideal.span {B.equivFun.symm ![-34, 0, 3]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 1375 ![![47, 0, 0], ![4, 1, 0]]
  ![-161, -9, 4] ![![1375, 0, 0], ![-312, 79, 1]] where
    su := ![![64625, 0, 0], ![5500, 1375, 0]]
    hsu := by decide
    w := ![![-221375, -12375, 5500], ![4125, -8250, -6875]]
    hw := by decide
    g := ![![![167, -169, 158], ![1127, -306, 0]], ![![256, -83, 22], ![1183, -44, 0]]]
    h := ![![![7882293, -5298407, -23789392], ![558136, 124233492, 0]], ![![-172159, 115721, 519581], ![-12157, -2713368, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {1375} * I47N1 =  Ideal.span {B.equivFun.symm ![-161, -9, 4]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E47RS1 


noncomputable def E61RS1 : RelationCertificate Table 275 ![![61, 0, 0], ![8, 1, 0]]
  ![-887, -75, 4] ![![275, 0, 0], ![113, 4, 1]] where
    su := ![![16775, 0, 0], ![2200, 275, 0]]
    hsu := by decide
    w := ![![-243925, -20625, 1100], ![-90475, -11550, -3300]]
    hw := by decide
    g := ![![![-24307728, 17993488, 6603576], ![-9702329, -46315022, 0]], ![![-3389559, 2509044, 920820], ![-1352719, -6458270, 0]]]
    h := ![![![-12845, 26010, 38986], ![-1257, -264238, 0]], ![![-4756, 9629, 14433], ![-461, -97825, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {275} * I61N1 =  Ideal.span {B.equivFun.symm ![-887, -75, 4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E61RS1 


noncomputable def E67RS0 : RelationCertificate Table 275 ![![67, 0, 0], ![2, 1, 0]]
  ![9337, -1090, 691] ![![275, 0, 0], ![113, 4, 1]] where
    su := ![![18425, 0, 0], ![550, 275, 0]]
    hsu := by decide
    w := ![![2567675, -299750, 190025], ![746900, -87175, 55275]]
    hw := by decide
    g := ![![![6807522, -5039259, -1849407], ![2717395, 12971008, 0]], ![![212726, -157477, -57794], ![84945, 405344, 0]]]
    h := ![![![262240559, -116828, -787422119], ![7826386, 5861920296, 0]], ![![76281980, -33984, -229049691], ![2276611, 1705147722, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {275} * I67N0 =  Ideal.span {B.equivFun.symm ![9337, -1090, 691]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 3125 ![![67, 0, 0], ![27, 1, 0]]
  ![1766, -206, 131] ![![3125, 0, 0], ![-812, 1079, 1]] where
    su := ![![209375, 0, 0], ![84375, 3125, 0]]
    hsu := by decide
    w := ![![5518750, -643750, 409375], ![-22796875, 2656250, -1681250]]
    hw := by decide
    g := ![![![420, -557, -1], ![1612, 0, 0]], ![![593, -786, -1], ![2276, 0, 0]]]
    h := ![![![-76529956, 706223620, 254131433], ![-20299746, -1891867320, 0]], ![![316122184, -2917197503, -1049740564], ![83852301, 7814735250, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3125} * I67N1 =  Ideal.span {B.equivFun.symm ![1766, -206, 131]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 34375 ![![67, 0, 0], ![-30, 1, 0]]
  ![6277, 163, -378] ![![34375, 0, 0], ![-13312, 1079, 1]] where
    su := ![![2303125, 0, 0], ![-1031250, 34375, 0]]
    hsu := by decide
    w := ![![215771875, 5603125, -12993750], ![-20453125, 3850000, 5396875]]
    hw := by decide
    g := ![![![626580287, 3116924630, -1954462063], ![-144850916, 6916283556, 0]], ![![-277712004, -1381494315, 866263404], ![64209279, -3065459012, 0]]]
    h := ![![![-16736939909, -200121840350, 56265347196], ![4507259133, -418864251390, 0]], ![![1598231906, 19109891690, -5372850302], ![-430403950, 39997885599, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {34375} * I67N2 =  Ideal.span {B.equivFun.symm ![6277, 163, -378]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E67RS2 


noncomputable def E71RS1 : RelationCertificate Table 34375 ![![71, 0, 0], ![25, 1, 0]]
  ![617, -60, -109] ![![34375, 0, 0], ![-13312, 1079, 1]] where
    su := ![![2440625, 0, 0], ![859375, 34375, 0]]
    hsu := by decide
    w := ![![21209375, -2062500, -3746875], ![10346875, 1478125, 515625]]
    hw := by decide
    g := ![![![671281875, 3339306868, -2093906313], ![-155192545, 7409736948, 0]], ![![252947182, 1258289513, -789008176], ![-58477345, 2792074792, 0]]]
    h := ![![![42984, -356959, -139625], ![10127, 1101474, 0]], ![![20865, -173367, -67812], ![4951, 534963, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {34375} * I71N1 =  Ideal.span {B.equivFun.symm ![617, -60, -109]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 1375 ![![73, 0, 0], ![-19, 1, 0]]
  ![-30649, 3579, -2269] ![![1375, 0, 0], ![-312, 79, 1]] where
    su := ![![100375, 0, 0], ![-26125, 1375, 0]]
    hsu := by decide
    w := ![![-42142375, 4921125, -3119875], ![36316500, -4240500, 2688125]]
    hw := by decide
    g := ![![![122, 137, -208], ![20, 402, 0]], ![![223, -97, 49], ![1114, -96, 0]]]
    h := ![![![977868, 7135784, -3057283], ![-156743, 24797710, 0]], ![![-842680, -6149312, 2634635], ![135092, -21369600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {1375} * I73N1 =  Ideal.span {B.equivFun.symm ![-30649, 3579, -2269]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 34375 ![![79, 0, 0], ![16, 1, 0]]
  ![-1027, 108, -70] ![![34375, 0, 0], ![-13312, 1079, 1]] where
    su := ![![2715625, 0, 0], ![550000, 34375, 0]]
    hsu := by decide
    w := ![![-35303125, 3712500, -2406250], ![25093750, -2853125, 1753125]]
    hw := by decide
    g := ![![![194855343, 969277715, -607784181], ![-45029027, 2150774784, 0]], ![![56831096, 282706139, -177270386], ![-13137888, 627309312, 0]]]
    h := ![![![5781, -27884, -17920], ![884, 157290, 0]], ![![-4136, 19852, 12759], ![-531, -111990, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {34375} * I79N1 =  Ideal.span {B.equivFun.symm ![-1027, 108, -70]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E79RS1 
