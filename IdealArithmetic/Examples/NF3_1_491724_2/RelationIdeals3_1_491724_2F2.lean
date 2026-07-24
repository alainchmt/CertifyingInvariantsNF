import IdealArithmetic.Examples.NF3_1_491724_2.PrimesBelow3_1_491724_2F2
import IdealArithmetic.Examples.NF3_1_491724_2.ClassGroupData3_1_491724_2

set_option linter.all false

noncomputable section


noncomputable def E101RS0 : RelationCertificate Table 49 ![![101, 0, 0], ![4, 1, 0]]
  ![-4349, -1188, -82] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![4949, 0, 0], ![196, 49, 0]]
    hsu := by decide
    w := ![![-213101, -58212, -4018], ![-119021, -32585, -2254]]
    hw := by decide
    g := ![![![667155, -131846910, -10146020], ![-2513740, 497154862, 0]], ![![25298, -5004095, -385080], ![-95386, 18868924, 0]]]
    h := ![![![-797865, -199800, -84], ![20145004, 8402, 0]], ![![-445625, -111593, -47], ![11251424, 4701, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {49} * I101N0 =  Ideal.span {B.equivFun.symm ![-4349, -1188, -82]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 49 ![![101, 0, 0], ![10, 1, 0]]
  ![5729, 1572, 109] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![4949, 0, 0], ![490, 49, 0]]
    hsu := by decide
    w := ![![280721, 77028, 5341], ![157535, 43169, 2989]]
    hw := by decide
    g := ![![![-591423, 116974819, 9001560], ![2230336, -441076577, 0]], ![![-72540, 14340506, 1103545], ![273452, -54073709, 0]]]
    h := ![![![2308139, 233543, 273], ![-23311631, -27464, 0]], ![![1295285, 131058, 153], ![-13082057, -15392, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {49} * I101N1 =  Ideal.span {B.equivFun.symm ![5729, 1572, 109]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 49 ![![101, 0, 0], ![-14, 1, 0]]
  ![-209, -36, -1] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![4949, 0, 0], ![-686, 49, 0]]
    hsu := by decide
    w := ![![-10241, -1764, -49], ![-3479, -833, -49]]
    hw := by decide
    g := ![![![133, -19199, -1478], ![-350, 72403, 0]], ![![-26, 2623, 202], ![66, -9894, 0]]]
    h := ![![![-156039, 11341, -14], ![-1125695, 1413, 0]], ![![-52981, 3854, -5], ![-382215, 504, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {49} * I101N2 =  Ideal.span {B.equivFun.symm ![-209, -36, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS2 


noncomputable def E103RS1 : RelationCertificate Table 7 ![![103, 0, 0], ![12, 1, 0]]
  ![-113, -6, 1] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![721, 0, 0], ![84, 7, 0]]
    hsu := by decide
    w := ![![-791, -42, 7], ![875, 49, -7]]
    hw := by decide
    g := ![![![2999, 149120, -152101], ![20878, 1064706, 0]], ![![397, 19788, -20184], ![2773, 141288, 0]]]
    h := ![![![-515, -55, -1], ![4411, 104, 0]], ![![551, 46, 0], ![-4719, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {7} * I103N1 =  Ideal.span {B.equivFun.symm ![-113, -6, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 49 ![![107, 0, 0], ![3, 1, 0]]
  ![68849, 3181, -550] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![5243, 0, 0], ![147, 49, 0]]
    hsu := by decide
    w := ![![3373601, 155869, -26950], ![475937, 24402, -3969]]
    hw := by decide
    g := ![![![16441, -22701, -1777], ![3912, 103312, 0]], ![![2652, -145, -16], ![747, 3432, 0]]]
    h := ![![![68821, 22771, 0], ![-2431666, -550, 0]], ![![9709, 3213, 0], ![-343050, -81, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {49} * I107N0 =  Ideal.span {B.equivFun.symm ![68849, 3181, -550]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E107RS0 


noncomputable def E107RS2 : RelationCertificate Table 7 ![![107, 0, 0], ![-8, 1, 0]]
  ![-227, -60, -4] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![749, 0, 0], ![-56, 7, 0]]
    hsu := by decide
    w := ![![-1589, -420, -28], ![-2821, -791, -56]]
    hw := by decide
    g := ![![![407, 52, -20], ![-48, 112, 0]], ![![-58, -6, 1], ![10, -3, 0]]]
    h := ![![![-12689, 1601, -2], ![-169687, 210, 0]], ![![-22545, 2832, -2], ![-301489, 206, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {7} * I107N2 =  Ideal.span {B.equivFun.symm ![-227, -60, -4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS2 


noncomputable def E109RS1 : RelationCertificate Table 49 ![![109, 0, 0], ![-51, 1, 0]]
  ![-85, -13, 1] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![5341, 0, 0], ![-2499, 49, 0]]
    hsu := by decide
    w := ![![-4165, -637, 49], ![-343, -98, 0]]
    hw := by decide
    g := ![![![1329090, -262752016, -20219558], ![-5009629, 990758340, 0]], ![![-612948, 121174067, 9324709], ![2310333, -456910740, 0]]]
    h := ![![![-279973, 6255, -15], ![-598372, 1636, 0]], ![![-22951, 552, -2], ![-49052, 218, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {49} * I109N1 =  Ideal.span {B.equivFun.symm ![-85, -13, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 7 ![![109, 0, 0], ![-5, 1, 0]]
  ![-39517, -3463, 429] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![763, 0, 0], ![-35, 7, 0]]
    hsu := by decide
    w := ![![-276619, -24241, 3003], ![366415, 30870, -3892]]
    hw := by decide
    g := ![![![-249091, -72711, -4902], ![25200, 776, 0]], ![![-21590, -6317, -411], ![2189, -30, 0]]]
    h := ![![![-43143, 8544, 0], ![-932614, 429, 0]], ![![57165, -11317, -1], ![1235728, -447, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {7} * I109N2 =  Ideal.span {B.equivFun.symm ![-39517, -3463, 429]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS2 


noncomputable def E127RS1 : RelationCertificate Table 7 ![![127, 0, 0], ![0, 1, 0]]
  ![-127, -6, 1] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![889, 0, 0], ![0, 7, 0]]
    hsu := by decide
    w := ![![-889, -42, 7], ![889, 35, -7]]
    hw := by decide
    g := ![![![5, 0, -1], ![6, 6, 0]], ![![-1, 0, 0], ![-1, 0, 0]]]
    h := ![![![-1, 0, 0], ![-6, 1, 0]], ![![1, 0, 0], ![5, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {7} * I127N1 =  Ideal.span {B.equivFun.symm ![-127, -6, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 49 ![![131, 0, 0], ![-1, 1, 0]]
  ![-5315, -369, 51] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![6419, 0, 0], ![-49, 49, 0]]
    hsu := by decide
    w := ![![-260435, -18081, 2499], ![-30233, -2156, 294]]
    hw := by decide
    g := ![![![-1657769, 327722185, 25219208], ![6248398, -1235741222, 0]], ![![1675, -333646, -25675], ![-6326, 1258072, 0]]]
    h := ![![![-80, 37, 0], ![-5165, 51, 0]], ![![-8, 3, 0], ![-431, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {49} * I131N1 =  Ideal.span {B.equivFun.symm ![-5315, -369, 51]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 49 ![![137, 0, 0], ![-36, 1, 0]]
  ![14465, 1166, -150] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![6713, 0, 0], ![-1764, 49, 0]]
    hsu := by decide
    w := ![![708785, 57134, -7350], ![73745, 6223, -784]]
    hw := by decide
    g := ![![![2501031, -494356442, -38042216], ![-9425366, 1864068978, 0]], ![![-654021, 129281156, 9948574], ![2464905, -487480188, 0]]]
    h := ![![![27171433, -800366, 1266], ![103401996, -173592, 0]], ![![2827009, -83247, 131], ![10758298, -17963, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {49} * I137N1 =  Ideal.span {B.equivFun.symm ![14465, 1166, -150]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E137RS1 
