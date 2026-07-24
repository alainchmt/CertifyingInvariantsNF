import IdealArithmetic.Examples.NF3_1_662796_2.PrimesBelow3_1_662796_2F2
import IdealArithmetic.Examples.NF3_1_662796_2.ClassGroupData3_1_662796_2

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 833 ![![89, 0, 0], ![32, 1, 0]]
  ![299, 36, 2] ![![833, 0, 0], ![314, -2, 1]] where
    su := ![![74137, 0, 0], ![26656, 833, 0]]
    hsu := by decide
    w := ![![249067, 29988, 1666], ![108290, 13328, 833]]
    hw := by decide
    g := ![![![19815, 18926, -351], ![8311, -40590, 0]], ![![7466, 7119, -132], ![3094, -15268, 0]]]
    h := ![![![2359, -77902, -7082], ![14, 210100, 0]], ![![1026, -33869, -3079], ![5, 91344, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {833} * I89N1 =  Ideal.span {B.equivFun.symm ![299, 36, 2]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 119 ![![97, 0, 0], ![-28, 1, 0]]
  ![-153, -46, -8] ![![119, 0, 0], ![-46, 1, 0]] where
    su := ![![11543, 0, 0], ![-3332, 119, 0]]
    hsu := by decide
    w := ![![-18207, -5474, -952], ![3332, 1309, 238]]
    hw := by decide
    g := ![![![-6054327, -273217813, 18214496], ![44421, -722508340, 0]], ![![1657506, 74797271, -4986478], ![-12038, 197796960, 0]]]
    h := ![![![1924, 51397, -5711], ![76, 184653, 0]], ![![-339, -9387, 1043], ![29, -33723, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {119} * I97N1 =  Ideal.span {B.equivFun.symm ![-153, -46, -8]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 17 ![![101, 0, 0], ![44, 1, 0]]
  ![423, 99, 16] ![![17, 0, 0], ![-43, -2, 1]] where
    su := ![![1717, 0, 0], ![748, 17, 0]]
    hsu := by decide
    w := ![![7191, 1683, 272], ![8024, 1887, 306]]
    hw := by decide
    g := ![![![50, -8, 1], ![-6, 0, 0]], ![![34, -2, 0], ![1, 0, 0]]]
    h := ![![![441323, -19789226, -1319284], ![-3575, 44415900, 0]], ![![492440, -22081192, -1472082], ![-3997, 49560100, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {17} * I101N1 =  Ideal.span {B.equivFun.symm ![423, 99, 16]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 7 ![![103, 0, 0], ![16, 1, 0]]
  ![-36, -3, 1] ![![7, 0, 0], ![3, 1, 0]] where
    su := ![![721, 0, 0], ![112, 7, 0]]
    hsu := by decide
    w := ![![-252, -21, 7], ![364, 28, -7]]
    hw := by decide
    g := ![![![307, -1129, -850], ![-24, 1983, 0]], ![![46, -180, -135], ![1, 315, 0]]]
    h := ![![![213, -3786, -668], ![60, 22935, 0]], ![![-328, 5468, 965], ![44, -33132, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {7} * I103N0 =  Ideal.span {B.equivFun.symm ![-36, -3, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 7 ![![103, 0, 0], ![-14, 1, 0]]
  ![-179, -12, 4] ![![7, 0, 0], ![3, 1, 0]] where
    su := ![![721, 0, 0], ![-98, 7, 0]]
    hsu := by decide
    w := ![![-1253, -84, 28], ![1351, 77, -28]]
    hw := by decide
    g := ![![![20443, -77526, -58390], ![-2306, 136242, 0]], ![![-4, -1, 0], ![6, 0, 0]]]
    h := ![![![885, 11396, -2630], ![74, 90298, 0]], ![![-940, -12294, 2837], ![28, -97405, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {7} * I103N1 =  Ideal.span {B.equivFun.symm ![-179, -12, 4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 7 ![![103, 0, 0], ![-2, 1, 0]]
  ![-93, -6, 2] ![![7, 0, 0], ![3, 1, 0]] where
    su := ![![721, 0, 0], ![-14, 7, 0]]
    hsu := by decide
    w := ![![-651, -42, 14], ![665, 35, -14]]
    hw := by decide
    g := ![![![2138, -8089, -6092], ![-235, 14214, 0]], ![![-50, 183, 138], ![6, -322, 0]]]
    h := ![![![31543, 31552, -94648], ![-280, 3249582, 0]], ![![-32227, -32239, 96706], ![382, -3320240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {7} * I103N2 =  Ideal.span {B.equivFun.symm ![-93, -6, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E103RS2 


noncomputable def E107RS0 : RelationCertificate Table 49 ![![107, 0, 0], ![3, 1, 0]]
  ![414, -18, -1] ![![49, 0, 0], ![-4, 1, 0]] where
    su := ![![5243, 0, 0], ![147, 49, 0]]
    hsu := by decide
    w := ![![20286, -882, -49], ![-2107, 392, -49]]
    hw := by decide
    g := ![![![10682735, 32105693, -32101264], ![-216834, 524320654, 0]], ![![387324, 1164048, -1163887], ![-7853, 19010156, 0]]]
    h := ![![![-730251, 2920185, 2190187], ![6867, -78116670, 0]], ![![76147, -304504, -228383], ![-704, 8145660, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {49} * I107N0 =  Ideal.span {B.equivFun.symm ![414, -18, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 7 ![![107, 0, 0], ![26, 1, 0]]
  ![-506, -118, -19] ![![7, 0, 0], ![3, 1, 0]] where
    su := ![![749, 0, 0], ![182, 7, 0]]
    hsu := by decide
    w := ![![-3542, -826, -133], ![-10311, -2422, -392]]
    hw := by decide
    g := ![![![279, -398, -307], ![71, 705, 0]], ![![52, -109, -83], ![11, 192, 0]]]
    h := ![![![10566, -285056, -31673], ![-54, 1129664, 0]], ![![30785, -829796, -92200], ![-270, 3288448, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {7} * I107N1 =  Ideal.span {B.equivFun.symm ![-506, -118, -19]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 833 ![![109, 0, 0], ![27, 1, 0]]
  ![-8007, -585, 188] ![![833, 0, 0], ![192, 1, 0]] where
    su := ![![90797, 0, 0], ![22491, 833, 0]]
    hsu := by decide
    w := ![![-6669831, -487305, 156604], ![-1448587, -106624, 34153]]
    hw := by decide
    g := ![![![-108277246233082, 20892019157259761, 324746414073463], ![123394814707, -90171254307731586, 0]], ![![-26489849552849, 5111197999420655, 79448674129448], ![30188338085, -22060248516610072, 0]]]
    h := ![![![-700957167, 19584812213, 2098378682], ![6045598, -76241092050, 0]], ![![-152236568, 4253504648, 455733932], ![1313012, -16558332849, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {833} * I109N1 =  Ideal.span {B.equivFun.symm ![-8007, -585, 188]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 49 ![![113, 0, 0], ![-33, 1, 0]]
  ![275, 69, 12] ![![49, 0, 0], ![-4, 1, 0]] where
    su := ![![5537, 0, 0], ![-1617, 49, 0]]
    hsu := by decide
    w := ![![13475, 3381, 588], ![4459, 980, 147]]
    hw := by decide
    g := ![![![-1340, -4143, 4143], ![45, -67680, 0]], ![![375, 1157, -1158], ![33, 18918, 0]]]
    h := ![![![-405, -13823, 1296], ![84, -48812, 0]], ![![-127, -4576, 429], ![52, -16158, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {49} * I113N1 =  Ideal.span {B.equivFun.symm ![275, 69, 12]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 7 ![![113, 0, 0], ![-20, 1, 0]]
  ![222, 15, -5] ![![7, 0, 0], ![3, 1, 0]] where
    su := ![![791, 0, 0], ![-140, 7, 0]]
    hsu := by decide
    w := ![![1554, 105, -35], ![-1694, -98, 35]]
    hw := by decide
    g := ![![![-75, 193, 148], ![2, -347, 0]], ![![9, -32, -24], ![1, 56, 0]]]
    h := ![![![-144707, -2753732, 434798], ![1264, -16377393, 0]], ![![157780, 3002119, -474017], ![-1263, 17854642, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {7} * I113N2 =  Ideal.span {B.equivFun.symm ![222, 15, -5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E113RS2 


noncomputable def E127RS0 : RelationCertificate Table 119 ![![127, 0, 0], ![6, 1, 0]]
  ![65, -1, -2] ![![119, 0, 0], ![-43, -2, 1]] where
    su := ![![15113, 0, 0], ![714, 119, 0]]
    hsu := by decide
    w := ![![7735, -119, -238], ![-714, -119, 0]]
    hw := by decide
    g := ![![![-1092, -75, 15], ![431, 313, 0]], ![![-73, -5, 1], ![27, 21, 0]]]
    h := ![![![-490, 3418, 1465], ![46, -62019, 0]], ![![39, -316, -135], ![126, 5715, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {119} * I127N0 =  Ideal.span {B.equivFun.symm ![65, -1, -2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 833 ![![127, 0, 0], ![54, 1, 0]]
  ![7926, 1854, 299] ![![833, 0, 0], ![314, -2, 1]] where
    su := ![![105791, 0, 0], ![44982, 833, 0]]
    hsu := by decide
    w := ![![6602358, 1544382, 249067], ![2980474, 697221, 112455]]
    hw := by decide
    g := ![![![3515998948, 3308636035, -61216266], ![1317341203, -7096544167, 0]], ![![1605185604, 1510516818, -27947529], ![601416315, -3239839375, 0]]]
    h := ![![![-263284344, 14439686828, 787620035], ![1750708, -33342581382, 0]], ![![-118853277, 6518442954, 355551774], ![790334, -15051691721, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {833} * I127N1 =  Ideal.span {B.equivFun.symm ![7926, 1854, 299]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 17 ![![127, 0, 0], ![-60, 1, 0]]
  ![215, 50, 8] ![![17, 0, 0], ![-43, -2, 1]] where
    su := ![![2159, 0, 0], ![-1020, 17, 0]]
    hsu := by decide
    w := ![![3655, 850, 136], ![4097, 952, 153]]
    hw := by decide
    g := ![![![-52, 0, -1], ![133, 0, 0]], ![![52, 1, 0], ![-62, 0, 0]]]
    h := ![![![-595, -36264, 1844], ![38, -78060, 0]], ![![-637, -40650, 2067], ![106, -87500, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {17} * I127N2 =  Ideal.span {B.equivFun.symm ![215, 50, 8]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E127RS2 


noncomputable def E131RS0 : RelationCertificate Table 17 ![![131, 0, 0], ![1, 1, 0]]
  ![-731, -58, 18] ![![17, 0, 0], ![5, 1, 0]] where
    su := ![![2227, 0, 0], ![17, 17, 0]]
    hsu := by decide
    w := ![![-12427, -986, 306], ![4845, 289, -102]]
    hw := by decide
    g := ![![![2368615, -13981859, -6994635], ![-125809, 39636279, 0]], ![![36202, -213666, -106890], ![-1913, 605712, 0]]]
    h := ![![![220, -453, -678], ![61, 29612, 0]], ![![-88, 180, 270], ![21, -11792, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {17} * I131N0 =  Ideal.span {B.equivFun.symm ![-731, -58, 18]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E131RS0 


noncomputable def E131RS1 : RelationCertificate Table 17 ![![131, 0, 0], ![37, 1, 0]]
  ![-187, -11, 4] ![![17, 0, 0], ![5, 1, 0]] where
    su := ![![2227, 0, 0], ![629, 17, 0]]
    hsu := by decide
    w := ![![-3179, -187, 68], ![952, 51, -17]]
    hw := by decide
    g := ![![![183223, -1081549, -541061], ![-9727, 3066012, 0]], ![![76905, -453984, -227112], ![-4076, 1286968, 0]]]
    h := ![![![5945, -225771, -17824], ![-18, 778316, 0]], ![![-1808, 67614, 5338], ![103, -233093, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {17} * I131N1 =  Ideal.span {B.equivFun.symm ![-187, -11, 4]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E131RS1 


noncomputable def E131RS2 : RelationCertificate Table 17 ![![131, 0, 0], ![-38, 1, 0]]
  ![68, 10, 1] ![![17, 0, 0], ![5, 1, 0]] where
    su := ![![2227, 0, 0], ![-646, 17, 0]]
    hsu := by decide
    w := ![![1156, 170, 17], ![799, 204, 34]]
    hw := by decide
    g := ![![![-91, 425, 214], ![8, -1210, 0]], ![![21, -114, -57], ![16, 322, 0]]]
    h := ![![![372, 13036, -1057], ![66, 46156, 0]], ![![279, 8978, -728], ![124, 31790, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {17} * I131N2 =  Ideal.span {B.equivFun.symm ![68, 10, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E131RS2 


noncomputable def E137RS1 : RelationCertificate Table 119 ![![137, 0, 0], ![27, 1, 0]]
  ![202, -17, 1] ![![119, 0, 0], ![-43, -2, 1]] where
    su := ![![16303, 0, 0], ![3213, 119, 0]]
    hsu := by decide
    w := ![![24038, -2023, 119], ![-17969, -952, 357]]
    hw := by decide
    g := ![![![312292851, 21344277, -4297830], ![-113240073, -89240276, 0]], ![![64295621, 4394412, -884848], ![-23314045, -18372998, 0]]]
    h := ![![![-1585760, 44339645, 4750685], ![11162, -216947948, 0]], ![![1182921, -33076200, -3543885], ![-8256, 161837416, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {119} * I137N1 =  Ideal.span {B.equivFun.symm ![202, -17, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E137RS1 
