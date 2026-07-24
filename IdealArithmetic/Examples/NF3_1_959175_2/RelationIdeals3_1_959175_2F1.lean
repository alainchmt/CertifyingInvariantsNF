import IdealArithmetic.Examples.NF3_1_959175_2.PrimesBelow3_1_959175_2F1
import IdealArithmetic.Examples.NF3_1_959175_2.ClassGroupData3_1_959175_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 3211 ![![37, 0, 0], ![-13, 1, 0]]
  ![2238, 77, 143] ![![3211, 0, 0], ![238, 1, 0]] where
    su := ![![118807, 0, 0], ![-41743, 3211, 0]]
    hsu := by decide
    w := ![![7186218, 247247, 459173], ![558714, 19266, 35321]]
    hw := by decide
    g := ![![![-7901094, 374575621, 20633509], ![-468689, -5096448570, -1525]], ![![2512687, -119127268, -6562129], ![150659, 1620836910, 485]]]
    h := ![![![558057552, 1832599015, -1584819899], ![-146544548, 4510641262, 0]], ![![43387663, 142480241, -123216001], ![-11393471, 350691696, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {3211} * I37N1 =  Ideal.span {B.equivFun.symm ![2238, 77, 143]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 13 ![![43, 0, 0], ![13, 1, 0]]
  ![17, -2, 0] ![![13, 0, 0], ![4, 1, 0]] where
    su := ![![559, 0, 0], ![169, 13, 0]]
    hsu := by decide
    w := ![![221, -26, 0], ![78, 13, -26]]
    hw := by decide
    g := ![![![22569, -1593, 800], ![6835, 0, -1734]], ![![7729, -546, 274], ![2345, 0, -594]]]
    h := ![![![10174, -24127, -28444], ![2535, 94084, 0]], ![![3491, -8276, -9757], ![866, 32273, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {13} * I43N1 =  Ideal.span {B.equivFun.symm ![17, -2, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E43RS1 


noncomputable def E47RS0 : RelationCertificate Table 19 ![![47, 0, 0], ![9, 1, 0]]
  ![-27, 2, 1] ![![19, 0, 0], ![-9, 1, 0]] where
    su := ![![893, 0, 0], ![171, 19, 0]]
    hsu := by decide
    w := ![![-513, 38, 19], ![418, -57, 19]]
    hw := by decide
    g := ![![![-92334, -237355, 278567], ![31252, -407136, 0]], ![![-80791, -207686, 243746], ![27351, -356244, 0]]]
    h := ![![![-767, 1104, 2046], ![-107, -7397, 0]], ![![620, -903, -1672], ![123, 6045, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {19} * I47N0 =  Ideal.span {B.equivFun.symm ![-27, 2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 247 ![![47, 0, 0], ![10, 1, 0]]
  ![-6732, -274, -403] ![![247, 0, 0], ![-9, 1, 0]] where
    su := ![![11609, 0, 0], ![2470, 247, 0]]
    hsu := by decide
    w := ![![-1662804, -67678, -99541], ![-12597, -494, -741]]
    hw := by decide
    g := ![![![342265, 758872, -896602], ![-9167, 17037078, 3048]], ![![75461, 167312, -197678], ![-2007, 3756243, 672]]]
    h := ![![![-500556, 832760, 1350167], ![-88762, -4881404, 0]], ![![-3793, 6309, 10229], ![-669, -36982, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {247} * I47N1 =  Ideal.span {B.equivFun.symm ![-6732, -274, -403]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 3211 ![![47, 0, 0], ![-19, 1, 0]]
  ![-2123, -63, -117] ![![3211, 0, 0], ![238, 1, 0]] where
    su := ![![150917, 0, 0], ![-61009, 3211, 0]]
    hsu := by decide
    w := ![![-6816953, -202293, -375687], ![-526604, -16055, -28899]]
    hw := by decide
    g := ![![![55623901, -2637010036, -145259190], ![3302275, 35878965876, 2928]], ![![-21885052, 1037512222, 57151161], ![-1296060, -14116315500, -1152]]]
    h := ![![![-1274075739, -6016499503, 3719401881], ![387041270, -13447068348, 0]], ![![-98419380, -464760627, 287315165], ![29898076, -1038754828, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {3211} * I47N2 =  Ideal.span {B.equivFun.symm ![-2123, -63, -117]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E47RS2 


noncomputable def E53RS1 : RelationCertificate Table 361 ![![53, 0, 0], ![-20, 1, 0]]
  ![202, -3, 8] ![![361, 0, 0], ![48, 1, 0]] where
    su := ![![19133, 0, 0], ![-7220, 361, 0]]
    hsu := by decide
    w := ![![72922, -1083, 2888], ![11191, 0, 361]]
    hw := by decide
    g := ![![![-6172, 57413, 16225], ![-513, -450556, 0]], ![![1665, -15889, -4490], ![465, 124684, 0]]]
    h := ![![![4664, 22671, -13382], ![-1290, 54558, 0]], ![![717, 3478, -2053], ![-194, 8370, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {361} * I53N1 =  Ideal.span {B.equivFun.symm ![202, -3, 8]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 361 ![![59, 0, 0], ![19, 1, 0]]
  ![-159, -3, 8] ![![361, 0, 0], ![48, 1, 0]] where
    su := ![![21299, 0, 0], ![6859, 361, 0]]
    hsu := by decide
    w := ![![-57399, -1083, 2888], ![-6137, -361, 361]]
    hw := by decide
    g := ![![![-3858, 35810, 10120], ![-261, -281025, 0]], ![![-1243, 11564, 3268], ![-106, -90750, 0]]]
    h := ![![![-1052, 3850, 2941], ![-254, -13347, 0]], ![![-113, 411, 314], ![-25, -1425, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {361} * I59N1 =  Ideal.span {B.equivFun.symm ![-159, -3, 8]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 19 ![![61, 0, 0], ![-18, 1, 0]]
  ![11, 2, 1] ![![19, 0, 0], ![-9, 1, 0]] where
    su := ![![1159, 0, 0], ![-342, 19, 0]]
    hsu := by decide
    w := ![![209, 38, 19], ![76, -19, 19]]
    hw := by decide
    g := ![![![-1742, -4481, 5259], ![592, -7686, 0]], ![![521, 1327, -1558], ![-166, 2277, 0]]]
    h := ![![![42279, 180471, -117205], ![-9489, 549962, 0]], ![![15535, 66272, -43040], ![-3453, 201957, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {19} * I61N1 =  Ideal.span {B.equivFun.symm ![11, 2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E61RS1 


noncomputable def E73RS1 : RelationCertificate Table 4693 ![![73, 0, 0], ![-10, 1, 0]]
  ![5228, 194, 325] ![![4693, 0, 0], ![2214, 1, 0]] where
    su := ![![342589, 0, 0], ![-46930, 4693, 0]]
    hsu := by decide
    w := ![![24535004, 910442, 1525225], ![11633947, 431756, 722722]]
    hw := by decide
    g := ![![![-548020852, 283782270978, 1667798770], ![-198063699, -602075045050, -1824]], ![![63693457, -32983471581, -193845067], ![23024721, 69978033050, 212]]]
    h := ![![![54056, 131471, -142337], ![-5565, 799302, 0]], ![![25638, 62340, -67493], ![-2596, 379011, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {4693} * I73N1 =  Ideal.span {B.equivFun.symm ![5228, 194, 325]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 247 ![![79, 0, 0], ![36, 1, 0]]
  ![636, -45, -13] ![![247, 0, 0], ![-9, 1, 0]] where
    su := ![![19513, 0, 0], ![8892, 247, 0]]
    hsu := by decide
    w := ![![157092, -11115, -3211], ![-7904, 1235, -494]]
    hw := by decide
    g := ![![![208625, 457028, -540191], ![-5642, 10262872, -1428]], ![![95262, 208676, -246648], ![-2477, 4685968, -652]]]
    h := ![![![7479927, -59139747, -22599382], ![2659998, 137334705, 0]], ![![-379259, 2998564, 1145857], ![-134861, -6963285, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {247} * I79N1 =  Ideal.span {B.equivFun.symm ![636, -45, -13]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS1 
