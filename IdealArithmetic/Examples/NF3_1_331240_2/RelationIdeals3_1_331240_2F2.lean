import IdealArithmetic.Examples.NF3_1_331240_2.PrimesBelow3_1_331240_2F2
import IdealArithmetic.Examples.NF3_1_331240_2.ClassGroupData3_1_331240_2

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 6 ![![97, 0, 0], ![21, 1, 0]]
  ![-2, -2, 1] ![![6, 0, 0], ![-2, 1, 0]] where
    su := ![![582, 0, 0], ![126, 6, 0]]
    hsu := by decide
    w := ![![-12, -12, 6], ![114, 12, -18]]
    hw := by decide
    g := ![![![1, 38, -63], ![11, 34, 0]], ![![-57, -1154, 1857], ![-167, -1013, 0]]]
    h := ![![![-26, -10, -6], ![120, 53, 0]], ![![-152, -13, -4], ![703, 35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {6} * I97N1 =  Ideal.span {B.equivFun.symm ![-2, -2, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 3 ![![101, 0, 0], ![-35, 1, 0]]
  ![7, -2, 1] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![303, 0, 0], ![-105, 3, 0]]
    hsu := by decide
    w := ![![21, -6, 3], ![117, 15, -15]]
    hw := by decide
    g := ![![![-863, 8804, -26633], ![2648, 7264, 0]], ![![105, -1101, 3329], ![-330, -908, 0]]]
    h := ![![![147, 14, -5], ![424, 46, 0]], ![![699, 9, -8], ![2016, 73, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {3} * I101N1 =  Ideal.span {B.equivFun.symm ![7, -2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 2 ![![107, 0, 0], ![-13, 1, 0]]
  ![2544, 856, -693] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![214, 0, 0], ![-26, 2, 0]]
    hsu := by decide
    w := ![![5088, 1712, -1386], ![-76230, -1736, 5258]]
    hw := by decide
    g := ![![![-7580937, -357532, -824450], ![-178765, 0, 0]], ![![73483, 3471, 7975], ![1737, 3, 0]]]
    h := ![![![10650, -820, 0], ![87462, -63, 0]], ![![-159514, 12563, -176], ![-1309991, 1951, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {2} * I107N1 =  Ideal.span {B.equivFun.symm ![2544, 856, -693]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 18 ![![109, 0, 0], ![15, 1, 0]]
  ![82, 10, -11] ![![18, 0, 0], ![4, 1, 0]] where
    su := ![![1962, 0, 0], ![270, 18, 0]]
    hsu := by decide
    w := ![![1476, 180, -198], ![-882, 72, 0]]
    hw := by decide
    g := ![![![-24, 124, -1386], ![7, 2264, 0]], ![![-12, 348, -3850], ![29, 6299, 0]]]
    h := ![![![-17, 6609, 7271], ![129, -72050, 0]], ![![-1, -3960, -4356], ![4, 43164, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {18} * I109N1 =  Ideal.span {B.equivFun.symm ![82, 10, -11]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 6 ![![113, 0, 0], ![44, 1, 0]]
  ![1082, 494, -379] ![![6, 0, 0], ![-2, 1, 0]] where
    su := ![![678, 0, 0], ![264, 6, 0]]
    hsu := by decide
    w := ![![6492, 2964, -2274], ![-43854, -2376, 3918]]
    hw := by decide
    g := ![![![182173, -1115009, 1869970], ![-246553, -1004302, 0]], ![![388590118, 7769445733, -12514320582], ![1165377588, 6826000811, 0]]]
    h := ![![![6418, 130, -9], ![-16458, 58, 0]], ![![-43437, -1148, -39], ![111388, 460, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {6} * I113N1 =  Ideal.span {B.equivFun.symm ![1082, 494, -379]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E113RS1 


noncomputable def E131RS0 : RelationCertificate Table 6 ![![131, 0, 0], ![19, 1, 0]]
  ![-29, 1, 1] ![![6, 0, 0], ![-2, -1, 1]] where
    su := ![![786, 0, 0], ![114, 6, 0]]
    hsu := by decide
    w := ![![-174, 6, 6], ![168, 42, -36]]
    hw := by decide
    g := ![![![-2143, 54, -6], ![708, 131, 0]], ![![-291, 8, -1], ![100, 18, 0]]]
    h := ![![![-2731, -159, -12], ![18828, 143, 0]], ![![2570, 129, -5], ![-17718, 59, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N0 : Ideal.span {6} * I131N0 =  Ideal.span {B.equivFun.symm ![-29, 1, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E131RS0 


noncomputable def E131RS1 : RelationCertificate Table 6 ![![131, 0, 0], ![45, 1, 0]]
  ![11687, 689, 1271] ![![6, 0, 0], ![-2, -1, 1]] where
    su := ![![786, 0, 0], ![270, 6, 0]]
    hsu := by decide
    w := ![![70122, 4134, 7626], ![52416, 3090, 5700]]
    hw := by decide
    g := ![![![4641, -136, 42], ![-1516, -297, 0]], ![![1655, -50, 15], ![-540, -104, 0]]]
    h := ![![![1784917, 45331, 1567], ![-5195832, -18546, 0]], ![![1334226, 33891, 1173], ![-3883886, -13883, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {6} * I131N1 =  Ideal.span {B.equivFun.symm ![11687, 689, 1271]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E131RS1 


noncomputable def E131RS2 : RelationCertificate Table 6 ![![131, 0, 0], ![-65, 1, 0]]
  ![37, 37, -26] ![![6, 0, 0], ![-2, -1, 1]] where
    su := ![![786, 0, 0], ![-390, 6, 0]]
    hsu := by decide
    w := ![![222, 222, -156], ![3996, -186, -96]]
    hw := by decide
    g := ![![![207, -101, -420], ![-118, -165, 0]], ![![-283, 47, 168], ![121, 79, 0]]]
    h := ![![![102, 14392, -2262], ![205, 26936, 0]], ![![262356, -4909, 137], ![528738, -1633, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {6} * I131N2 =  Ideal.span {B.equivFun.symm ![37, 37, -26]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E131RS2 


noncomputable def E137RS1 : RelationCertificate Table 2 ![![137, 0, 0], ![65, 1, 0]]
  ![-4765963, -280965, -518313] ![![2, 0, 0], ![-2, -1, 1]] where
    su := ![![274, 0, 0], ![130, 2, 0]]
    hsu := by decide
    w := ![![-9531926, -561930, -1036626], ![-21374224, -1260062, -2324512]]
    hw := by decide
    g := ![![![-2873, -1077, 414], ![3621, 0, 0]], ![![-329, -829, 438], ![966, 0, 0]]]
    h := ![![![-471469454, -8451732, -223204], ![993639219, 2732785, 0]], ![![-1057214796, -18951951, -500497], ![2228119076, 6127803, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {2} * I137N1 =  Ideal.span {B.equivFun.symm ![-4765963, -280965, -518313]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E137RS1 
