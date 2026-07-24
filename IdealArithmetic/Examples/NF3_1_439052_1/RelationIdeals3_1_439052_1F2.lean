import IdealArithmetic.Examples.NF3_1_439052_1.PrimesBelow3_1_439052_1F2
import IdealArithmetic.Examples.NF3_1_439052_1.ClassGroupData3_1_439052_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 38 ![![83, 0, 0], ![-32, 1, 0]]
  ![702, -42, -17] ![![38, 0, 0], ![3, 1, 0]] where
    su := ![![3154, 0, 0], ![-1216, 38, 0]]
    hsu := by decide
    w := ![![26676, -1596, -646], ![6688, -342, -152]]
    hw := by decide
    g := ![![![310, 1008, 669], ![73, -12726, 0]], ![![-117, -383, -253], ![4, 4815, 0]]]
    h := ![![![1369920, -59126706, 3696353], ![-1240500, -153398658, 0]], ![![343437, -14821951, 926606], ![-310908, -38454151, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {38} * I83N1 =  Ideal.span {B.equivFun.symm ![702, -42, -17]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 190 ![![89, 0, 0], ![18, 1, 0]]
  ![591, -87, -23] ![![190, 0, 0], ![-133, 9, 2]] where
    su := ![![16910, 0, 0], ![3420, 190, 0]]
    hsu := by decide
    w := ![![112290, -16530, -4370], ![29260, 1330, -190]]
    hw := by decide
    g := ![![![-2342, -259, 117], ![1812, -1287, 0]], ![![-598, -67, 30], ![484, -333, 0]]]
    h := ![![![531273, 10375897, 1153157], ![224044, -51315498, 0]], ![![133241, 2602501, 289237], ![56264, -12871047, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {190} * I89N1 =  Ideal.span {B.equivFun.symm ![591, -87, -23]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 5 ![![97, 0, 0], ![-31, 1, 0]]
  ![-28, 7, -1] ![![5, 0, 0], ![-39, 2, 1]] where
    su := ![![485, 0, 0], ![-155, 5, 0]]
    hsu := by decide
    w := ![![-140, 35, -5], ![-145, 50, -10]]
    hw := by decide
    g := ![![![5, -6, -1], ![-4, 0, 0]], ![![9, 1, 0], ![2, 0, 0]]]
    h := ![![![171, -5874, 379], ![-57, -18382, 0]], ![![190, -6107, 394], ![-21, -19110, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {5} * I97N1 =  Ideal.span {B.equivFun.symm ![-28, 7, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 190 ![![101, 0, 0], ![21, 1, 0]]
  ![196, -52, 7] ![![190, 0, 0], ![-133, 9, 2]] where
    su := ![![19190, 0, 0], ![3990, 190, 0]]
    hsu := by decide
    w := ![![37240, -9880, 1330], ![-16910, 4940, -760]]
    hw := by decide
    g := ![![![-2946, -316, 145], ![2242, -1599, 0]], ![![-550, -74, 30], ![607, -345, 0]]]
    h := ![![![-2637685, -60384873, -5752021], ![-1146223, 290477064, 0]], ![![1198127, 27429182, 2612794], ![520723, -131946099, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {190} * I101N1 =  Ideal.span {B.equivFun.symm ![196, -52, 7]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 190 ![![101, 0, 0], ![-35, 1, 0]]
  ![123, -21, 1] ![![190, 0, 0], ![-133, 9, 2]] where
    su := ![![19190, 0, 0], ![-6650, 190, 0]]
    hsu := by decide
    w := ![![23370, -3990, 190], ![-7790, 1900, -190]]
    hw := by decide
    g := ![![![-992, -117, 51], ![893, -572, 0]], ![![450, 32, -19], ![-140, 194, 0]]]
    h := ![![![1376878, -61330982, 3505241], ![-1084289, -177014670, 0]], ![![-459391, 20463560, -1169551], ![361825, 59062325, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {190} * I101N2 =  Ideal.span {B.equivFun.symm ![123, -21, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E101RS2 


noncomputable def E103RS1 : RelationCertificate Table 5 ![![103, 0, 0], ![-15, 1, 0]]
  ![128, -13, -4] ![![5, 0, 0], ![-39, 2, 1]] where
    su := ![![515, 0, 0], ![-75, 5, 0]]
    hsu := by decide
    w := ![![640, -65, -20], ![1130, 65, -5]]
    hw := by decide
    g := ![![![29, 39, -13], ![27, 0, 0]], ![![8, -11, 3], ![-5, 0, 0]]]
    h := ![![![-1021, 16136, -2152], ![369, 110826, 0]], ![![-1808, 28397, -3787], ![572, 195030, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {5} * I103N1 =  Ideal.span {B.equivFun.symm ![128, -13, -4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 5 ![![107, 0, 0], ![10, 1, 0]]
  ![10, 1, 0] ![![5, 0, 0], ![-39, 2, 1]] where
    su := ![![535, 0, 0], ![50, 5, 0]]
    hsu := by decide
    w := ![![50, 5, 0], ![-660, 35, 15]]
    hw := by decide
    g := ![![![23, 1, -1], ![3, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-196, -1960, -392], ![1, 20972, 0]], ![![2542, 25920, 5185], ![527, -277396, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {5} * I107N0 =  Ideal.span {B.equivFun.symm ![10, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 38 ![![107, 0, 0], ![26, 1, 0]]
  ![-103, 25, -3] ![![38, 0, 0], ![3, 1, 0]] where
    su := ![![4066, 0, 0], ![988, 38, 0]]
    hsu := by decide
    w := ![![-3914, 950, -114], ![532, -190, 38]]
    hw := by decide
    g := ![![![-1236710, -3751527, -2504462], ![-196329, 47584768, 0]], ![![-325238, -986603, -658641], ![-51629, 12514176, 0]]]
    h := ![![![243240, 7117119, 547561], ![125682, -29294515, 0]], ![![-33135, -968952, -74547], ![-17031, 3988265, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {38} * I107N1 =  Ideal.span {B.equivFun.symm ![-103, 25, -3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 190 ![![107, 0, 0], ![-37, 1, 0]]
  ![776, -12, -13] ![![190, 0, 0], ![-133, 9, 2]] where
    su := ![![20330, 0, 0], ![-7030, 190, 0]]
    hsu := by decide
    w := ![![147440, -2280, -2470], ![-62130, 3800, 1520]]
    hw := by decide
    g := ![![![568334708, 58218040, -27430426], ![-395365307, 300125574, 0]], ![![-192370668, -19705722, 9284687], ![133823812, -101586906, 0]]]
    h := ![![![-2492, 118656, -6415], ![2048, 343196, 0]], ![![1076, -50089, 2708], ![-795, -144874, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {190} * I107N2 =  Ideal.span {B.equivFun.symm ![776, -12, -13]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E107RS2 


noncomputable def E109RS0 : RelationCertificate Table 5 ![![109, 0, 0], ![0, 1, 0]]
  ![0, 1, 0] ![![5, 0, 0], ![-39, 2, 1]] where
    su := ![![545, 0, 0], ![0, 5, 0]]
    hsu := by decide
    w := ![![0, 5, 0], ![-270, 15, 5]]
    hw := by decide
    g := ![![![0, -247, 2], ![600, 0, -36]], ![![0, -131, 1], ![318, 0, -19]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![0, 0, 1], ![3, -54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {5} * I109N0 =  Ideal.span {B.equivFun.symm ![0, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E109RS0 


noncomputable def E113RS1 : RelationCertificate Table 38 ![![113, 0, 0], ![-19, 1, 0]]
  ![-628, 72, 21] ![![38, 0, 0], ![3, 1, 0]] where
    su := ![![4294, 0, 0], ![-722, 38, 0]]
    hsu := by decide
    w := ![![-23864, 2736, 798], ![-7524, 722, 228]]
    hw := by decide
    g := ![![![-161, -351, -243], ![9, 4584, 0]], ![![28, 54, 39], ![28, -732, 0]]]
    h := ![![![-14630, 294030, -30955], ![5074, 1748968, 0]], ![![-4602, 92687, -9758], ![1658, 551330, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {38} * I113N1 =  Ideal.span {B.equivFun.symm ![-628, 72, 21]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E113RS1 


noncomputable def E127RS1 : RelationCertificate Table 190 ![![127, 0, 0], ![-57, 1, 0]]
  ![-1776, 496, -77] ![![190, 0, 0], ![-133, 9, 2]] where
    su := ![![24130, 0, 0], ![-10830, 190, 0]]
    hsu := by decide
    w := ![![-337440, 94240, -14630], ![176130, -49020, 7600]]
    hw := by decide
    g := ![![![3426, 338, -162], ![-2169, 1764, 0]], ![![-1446, -156, 71], ![1084, -786, 0]]]
    h := ![![![2760, -235656, 8269], ![-3032, -525120, 0]], ![![-1413, 123000, -4316], ![1644, 274086, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {190} * I127N1 =  Ideal.span {B.equivFun.symm ![-1776, 496, -77]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E127RS1 


noncomputable def E137RS1 : RelationCertificate Table 190 ![![137, 0, 0], ![-53, 1, 0]]
  ![-2562, 88, 51] ![![190, 0, 0], ![-133, 9, 2]] where
    su := ![![26030, 0, 0], ![-10070, 190, 0]]
    hsu := by decide
    w := ![![-486780, 16720, 9690], ![157700, -11590, -4180]]
    hw := by decide
    g := ![![![-4115, -419, 197], ![3097, -2208, 0]], ![![1643, 149, -75], ![-1028, 828, 0]]]
    h := ![![![13309, -953451, 35983], ![-12055, -2464810, 0]], ![![-4277, 309274, -11672], ![4014, 799521, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {190} * I137N1 =  Ideal.span {B.equivFun.symm ![-2562, 88, 51]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E137RS1 
