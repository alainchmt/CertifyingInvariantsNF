import IdealArithmetic.Examples.NF3_3_240149_1.PrimesBelow3_3_240149_1F1
import IdealArithmetic.Examples.NF3_3_240149_1.ClassGroupData3_3_240149_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![-5, 1, 0]]
  ![-32, 1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![74, 0, 0], ![-10, 2, 0]]
    hsu := by decide
    w := ![![-64, 2, 2], ![-48, -8, 6]]
    hw := by decide
    g := ![![![-41, -6, -281], ![-1, 111, 0]], ![![10, -1, 37], ![0, -15, 0]]]
    h := ![![![204, -1047, 1048], ![-35, -7755, 0]], ![![150, -778, 779], ![-38, -5764, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![-32, 1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E37RS1 


noncomputable def E41RS0 : RelationCertificate Table 36 ![![41, 0, 0], ![0, 1, 0]]
  ![150, -53, -29] ![![36, 0, 0], ![6, 1, 0]] where
    su := ![![1476, 0, 0], ![0, 36, 0]]
    hsu := by decide
    w := ![![5400, -1908, -1044], ![2268, -864, -468]]
    hw := by decide
    g := ![![![547971306, 3470340091, 2896295607], ![187726912, -20853328369, 0]], ![![-193, -1202, -1003], ![-47, 7221, 0]]]
    h := ![![![3, -4, -4], ![111, 27, 0]], ![![1, -2, -3], ![58, 22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {36} * I41N0 =  Ideal.span {B.equivFun.symm ![150, -53, -29]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E41RS0 


noncomputable def E43RS1 : RelationCertificate Table 6 ![![43, 0, 0], ![-16, 1, 0]]
  ![-24, 1, 1] ![![6, 0, 0], ![0, 1, 0]] where
    su := ![![258, 0, 0], ![-96, 6, 0]]
    hsu := by decide
    w := ![![-144, 6, 6], ![-48, 0, 6]]
    hw := by decide
    g := ![![![-3530373, 0, -17651849], ![3, 21182219, 0]], ![![1314388, -1, 6571935], ![5, -7886322, 0]]]
    h := ![![![35, -646, 202], ![-13, -1737, 0]], ![![24, -215, 67], ![29, -576, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {6} * I43N1 =  Ideal.span {B.equivFun.symm ![-24, 1, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 12 ![![47, 0, 0], ![20, 1, 0]]
  ![6, 1, 1] ![![12, 0, 0], ![6, 1, 0]] where
    su := ![![564, 0, 0], ![240, 12, 0]]
    hsu := by decide
    w := ![![72, 12, 12], ![-12, 36, 12]]
    hw := by decide
    g := ![![![-20, -192, -161], ![-13, 386, 0]], ![![-9, -87, -73], ![-6, 175, 0]]]
    h := ![![![-1971, -56605, -14162], ![-2024, 133123, 0]], ![![350, 10184, 2548], ![375, -23951, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {12} * I47N1 =  Ideal.span {B.equivFun.symm ![6, 1, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E47RS1 


noncomputable def E61RS1 : RelationCertificate Table 9 ![![61, 0, 0], ![20, 1, 0]]
  ![-12, 4, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![549, 0, 0], ![180, 9, 0]]
    hsu := by decide
    w := ![![-108, 36, 9], ![-9, 0, 18]]
    hw := by decide
    g := ![![![-65, 177, -303], ![51, 547, 0]], ![![-22, 60, -103], ![19, 186, 0]]]
    h := ![![![4988, 124103, 31041], ![3721, -378700, 0]], ![![397, 10282, 2572], ![358, -31378, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {9} * I61N1 =  Ideal.span {B.equivFun.symm ![-12, 4, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E61RS1 


noncomputable def E73RS1 : RelationCertificate Table 18 ![![73, 0, 0], ![1, 1, 0]]
  ![-48, 25, 13] ![![18, 0, 0], ![6, 1, 0]] where
    su := ![![1314, 0, 0], ![18, 18, 0]]
    hsu := by decide
    w := ![![-864, 450, 234], ![-900, 414, 216]]
    hw := by decide
    g := ![![![-14491246, -108007460, -90507643], ![-10830825, 325827515, 0]], ![![-198513, -1479556, -1239832], ![-148360, 4463395, 0]]]
    h := ![![![-230, -229, -1144], ![37, 16705, 0]], ![![-212, -211, -1056], ![6, 15420, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {18} * I73N1 =  Ideal.span {B.equivFun.symm ![-48, 25, 13]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 12 ![![79, 0, 0], ![-39, 1, 0]]
  ![-90, 19, -5] ![![12, 0, 0], ![6, 1, 0]] where
    su := ![![948, 0, 0], ![-468, 12, 0]]
    hsu := by decide
    w := ![![-1080, 228, -60], ![-276, -96, 60]]
    hw := by decide
    g := ![![![-199247, -1962996, -1654110], ![-263196, 3969875, 0]], ![![93625, 922440, 777290], ![123683, -1865500, 0]]]
    h := ![![![57, -2652, 340], ![-20, -5373, 0]], ![![28, -507, 65], ![31, -1026, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {12} * I79N1 =  Ideal.span {B.equivFun.symm ![-90, 19, -5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E79RS1 
