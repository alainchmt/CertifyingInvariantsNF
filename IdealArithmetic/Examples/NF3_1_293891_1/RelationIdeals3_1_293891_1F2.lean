import IdealArithmetic.Examples.NF3_1_293891_1.PrimesBelow3_1_293891_1F2
import IdealArithmetic.Examples.NF3_1_293891_1.ClassGroupData3_1_293891_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![44, 1, 0]]
  ![-3375, -275, -101] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![178, 0, 0], ![88, 2, 0]]
    hsu := by decide
    w := ![![-6750, -550, -202], ![-12566, -1024, -376]]
    hw := by decide
    g := ![![![5211, -25784, -30879], ![-10285, 61770, 0]], ![![2610, -12894, -15440], ![-5140, 30885, 0]]]
    h := ![![![-65855, -2813, -31], ![133130, 2658, 0]], ![![-122619, -5250, -58], ![247882, 4974, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![-3375, -275, -101]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 32 ![![97, 0, 0], ![-47, 1, 0]]
  ![85, 15, -17] ![![32, 0, 0], ![-1, 1, 0]] where
    su := ![![3104, 0, 0], ![-1504, 32, 0]]
    hsu := by decide
    w := ![![2720, 480, -544], ![-1632, 512, 32]]
    hw := by decide
    g := ![![![-8155, -8052202, 8060024], ![-251373, -257921055, 0]], ![![3867, 3823012, -3826727], ![119368, 122455395, 0]]]
    h := ![![![160126, -3885, 10], ![330471, -987, 0]], ![![-96320, 2379, -7], ![-198787, 680, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {32} * I97N1 =  Ideal.span {B.equivFun.symm ![85, 15, -17]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E97RS1 


noncomputable def E101RS0 : RelationCertificate Table 2 ![![101, 0, 0], ![13, 1, 0]]
  ![17, -9, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![202, 0, 0], ![26, 2, 0]]
    hsu := by decide
    w := ![![34, -18, 2], ![108, -18, -8]]
    hw := by decide
    g := ![![![1029, -8154, -9896], ![-3561, 19747, 0]], ![![139, -1164, -1414], ![-512, 2821, 0]]]
    h := ![![![302, 23, 0], ![-2345, 1, 0]], ![![970, 75, 0], ![-7532, -4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {2} * I101N0 =  Ideal.span {B.equivFun.symm ![17, -9, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![21, 1, 0]]
  ![1, -3, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![202, 0, 0], ![42, 2, 0]]
    hsu := by decide
    w := ![![2, -6, 2], ![92, -28, -2]]
    hw := by decide
    g := ![![![257, -154, -143], ![52, 303, 0]], ![![59, -32, -28], ![15, 60, 0]]]
    h := ![![![5, 0, 0], ![-24, 1, 0]], ![![1154, 55, 0], ![-5548, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![1, -3, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 16 ![![101, 0, 0], ![-34, 1, 0]]
  ![1, 35, -13] ![![16, 0, 0], ![-1, 1, 0]] where
    su := ![![1616, 0, 0], ![-544, 16, 0]]
    hsu := by decide
    w := ![![16, 560, -208], ![-1184, 304, 48]]
    hw := by decide
    g := ![![![-3839, -798461, 801483], ![-49663, -12824080, 0]], ![![1248, 262396, -263391], ![16326, 4214365, 0]]]
    h := ![![![-1, 64, -2], ![-3, 189, 0]], ![![-62, 3, 0], ![-182, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {16} * I101N2 =  Ideal.span {B.equivFun.symm ![1, 35, -13]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E101RS2 


noncomputable def E107RS1 : RelationCertificate Table 2 ![![107, 0, 0], ![-40, 1, 0]]
  ![-25, 1, 3] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![214, 0, 0], ![-80, 2, 0]]
    hsu := by decide
    w := ![![-50, 2, 6], ![248, -102, 4]]
    hw := by decide
    g := ![![![-3654, 7906, 9103], ![2127, -18361, 0]], ![![1309, -2936, -3389], ![-813, 6832, 0]]]
    h := ![![![-1995, 91, -1], ![-5336, 110, 0]], ![![10052, -251, 0], ![26886, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {2} * I107N1 =  Ideal.span {B.equivFun.symm ![-25, 1, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 8 ![![109, 0, 0], ![20, 1, 0]]
  ![-41, 45, -11] ![![8, 0, 0], ![-1, 1, 0]] where
    su := ![![872, 0, 0], ![160, 8, 0]]
    hsu := by decide
    w := ![![-328, 360, -88], ![-960, 200, 56]]
    hw := by decide
    g := ![![![-2431, -302, -6], ![267, -542, 0]], ![![-506, -63, -2], ![62, -107, 0]]]
    h := ![![![-4969, -266, -1], ![27079, 98, 0]], ![![-14600, -771, -2], ![79564, 225, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {8} * I109N0 =  Ideal.span {B.equivFun.symm ![-41, 45, -11]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E109RS0 


noncomputable def E109RS2 : RelationCertificate Table 8 ![![109, 0, 0], ![-9, 1, 0]]
  ![19, 1, 1] ![![8, 0, 0], ![-1, 1, 0]] where
    su := ![![872, 0, 0], ![-72, 8, 0]]
    hsu := by decide
    w := ![![152, 8, 8], ![72, -8, 0]]
    hw := by decide
    g := ![![![436588, 28378213, -28814800], ![3492706, 230518401, 0]], ![![-37383, -2429942, 2467325], ![-299065, -19738600, 0]]]
    h := ![![![1387, -154, 0], ![16796, 1, 0]], ![![657, -73, 0], ![7956, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {8} * I109N2 =  Ideal.span {B.equivFun.symm ![19, 1, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E109RS2 


noncomputable def E127RS1 : RelationCertificate Table 2 ![![127, 0, 0], ![-26, 1, 0]]
  ![235, 19, 7] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![254, 0, 0], ![-52, 2, 0]]
    hsu := by decide
    w := ![![470, 38, 14], ![872, 72, 26]]
    hw := by decide
    g := ![![![-13, 153, 188], ![72, -381, 0]], ![![1, -32, -40], ![-15, 81, 0]]]
    h := ![![![2669, -101, 0], ![13028, 7, 0]], ![![4968, -188, 0], ![24250, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {2} * I127N1 =  Ideal.span {B.equivFun.symm ![235, 19, 7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E127RS1 


noncomputable def E137RS1 : RelationCertificate Table 4 ![![137, 0, 0], ![31, 1, 0]]
  ![-71, 7, 7] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![548, 0, 0], ![124, 4, 0]]
    hsu := by decide
    w := ![![-284, 28, 28], ![708, -260, 0]]
    hw := by decide
    g := ![![![-3521, 951, -1655], ![1122, 6165, 0]], ![![-868, 201, -373], ![271, 1380, 0]]]
    h := ![![![-5874, -222, -1], ![25957, 144, 0]], ![![14524, 499, 1], ![-64181, -137, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {4} * I137N1 =  Ideal.span {B.equivFun.symm ![-71, 7, 7]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E137RS1 
