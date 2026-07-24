import IdealArithmetic.Examples.NF3_1_406700_5.PrimesBelow3_1_406700_5F2
import IdealArithmetic.Examples.NF3_1_406700_5.ClassGroupData3_1_406700_5

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 289 ![![89, 0, 0], ![9, 1, 0]]
  ![16, -76, 43] ![![289, 0, 0], ![-53, 1, 0]] where
    su := ![![25721, 0, 0], ![2601, 289, 0]]
    hsu := by decide
    w := ![![4624, -21964, 12427], ![-289, 2023, -2312]]
    hw := by decide
    g := ![![![81, 165037, -3115], ![713, 899928, 0]], ![![6, 16954, -320], ![61, 92448, 0]]]
    h := ![![![2, -5, 0], ![-18, 43, 0]], ![![1, -17, -2], ![-10, 170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {289} * I89N1 =  Ideal.span {B.equivFun.symm ![16, -76, 43]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 289 ![![97, 0, 0], ![17, 1, 0]]
  ![14, -34, 5] ![![289, 0, 0], ![-100, 14, 1]] where
    su := ![![28033, 0, 0], ![4913, 289, 0]]
    hsu := by decide
    w := ![![4046, -9826, 1445], ![-867, 1734, -1156]]
    hw := by decide
    g := ![![![170, -1874, 192], ![-45, -3688, 0]], ![![113, -361, 35], ![227, -688, 0]]]
    h := ![![![72, 3, 0], ![-410, 5, 0]], ![![-47, -19, -1], ![268, 93, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {289} * I97N1 =  Ideal.span {B.equivFun.symm ![14, -34, 5]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 17 ![![101, 0, 0], ![-13, 1, 0]]
  ![-1081, 17, -23] ![![17, 0, 0], ![-1, 1, 0]] where
    su := ![![1717, 0, 0], ![-221, 17, 0]]
    hsu := by decide
    w := ![![-18377, 289, -391], ![782, -17, 17]]
    hw := by decide
    g := ![![![-1, -478, 478], ![-23, -8120, 0]], ![![1, 60, -61], ![17, 1036, 0]]]
    h := ![![![-252819, 19743, -23], ![-1964126, 2300, 0]], ![![10766, -828, 0], ![83640, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {17} * I101N1 =  Ideal.span {B.equivFun.symm ![-1081, 17, -23]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 17 ![![103, 0, 0], ![-14, 1, 0]]
  ![4, -15, 0] ![![17, 0, 0], ![36, -3, 1]] where
    su := ![![1751, 0, 0], ![-238, 17, 0]]
    hsu := by decide
    w := ![![68, -255, 0], ![-51, 153, 34]]
    hw := by decide
    g := ![![![-143, -30, 0], ![-225, 0, 0]], ![![-17, 7, -1], ![47, 0, 0]]]
    h := ![![![1020, -73, 0], ![7504, 0, 0]], ![![-723, 66, -1], ![-5319, 105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {17} * I103N1 =  Ideal.span {B.equivFun.symm ![4, -15, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 289 ![![107, 0, 0], ![-48, 1, 0]]
  ![31, -136, 22] ![![289, 0, 0], ![84, 1, 0]] where
    su := ![![30923, 0, 0], ![-13872, 289, 0]]
    hsu := by decide
    w := ![![8959, -39304, 6358], ![2890, -12427, 1734]]
    hw := by decide
    g := ![![![137, -206684, -2461], ![-544, 711099, 0]], ![![-158, 91793, 1093], ![576, -315819, 0]]]
    h := ![![![653, -5, 0], ![1455, 22, 0]], ![![254, -3, 0], ![566, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {289} * I107N1 =  Ideal.span {B.equivFun.symm ![31, -136, 22]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E107RS1 


noncomputable def E113RS0 : RelationCertificate Table 289 ![![113, 0, 0], ![47, 1, 0]]
  ![-12, 51, -14] ![![289, 0, 0], ![-100, 14, 1]] where
    su := ![![32657, 0, 0], ![13583, 289, 0]]
    hsu := by decide
    w := ![![-3468, 14739, -4046], ![-867, 2023, 2601]]
    hw := by decide
    g := ![![![-53, 3137, -321], ![352, 6204, 0]], ![![4, 1313, -135], ![224, 2604, 0]]]
    h := ![![![-55332, -1735, -12], ![133032, 1342, 0]], ![![-14350, -450, -3], ![34501, 348, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N0 : Ideal.span {289} * I113N0 =  Ideal.span {B.equivFun.symm ![-12, 51, -14]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E113RS0 


noncomputable def E113RS1 : RelationCertificate Table 289 ![![113, 0, 0], ![-33, 1, 0]]
  ![-28, 102, 7] ![![289, 0, 0], ![-100, 14, 1]] where
    su := ![![32657, 0, 0], ![-9537, 289, 0]]
    hsu := by decide
    w := ![![-8092, 29478, 2023], ![5491, -20230, 578]]
    hw := by decide
    g := ![![![131, 1003, -102], ![264, 2001, 0]], ![![82, -304, 28], ![271, -573, 0]]]
    h := ![![![-266, 11, 0], ![-910, 7, 0]], ![![197, -6, 0], ![674, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {289} * I113N1 =  Ideal.span {B.equivFun.symm ![-28, 102, 7]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E113RS1 


noncomputable def E113RS2 : RelationCertificate Table 289 ![![113, 0, 0], ![-15, 1, 0]]
  ![-346, 0, -7] ![![289, 0, 0], ![-100, 14, 1]] where
    su := ![![32657, 0, 0], ![-4335, 289, 0]]
    hsu := by decide
    w := ![![-99994, 0, -2023], ![33235, 0, 578]]
    hw := by decide
    g := ![![![2, 0, 0], ![7, 0, 0]], ![![21, -5, 0], ![60, -4, 0]]]
    h := ![![![-1551122, 105147, -116], ![-11685096, 13101, 0]], ![![515555, -34940, 38], ![3883840, -4292, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N2 : Ideal.span {289} * I113N2 =  Ideal.span {B.equivFun.symm ![-346, 0, -7]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E113RS2 


noncomputable def E127RS0 : RelationCertificate Table 289 ![![127, 0, 0], ![15, 1, 0]]
  ![6000, -93, 128] ![![289, 0, 0], ![-83, 14, 1]] where
    su := ![![36703, 0, 0], ![4335, 289, 0]]
    hsu := by decide
    w := ![![1734000, -26877, 36992], ![-474249, 7514, -10115]]
    hw := by decide
    g := ![![![-10577660, 132300357, -15350438], ![9393831, 295125512, 0]], ![![-1475917, 18460509, -2141922], ![1310891, 41180304, 0]]]
    h := ![![![11700, 776, 1], ![-98660, 1, 0]], ![![-3228, -225, -1], ![27221, 92, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {289} * I127N0 =  Ideal.span {B.equivFun.symm ![6000, -93, 128]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS0 


noncomputable def E127RS2 : RelationCertificate Table 289 ![![127, 0, 0], ![-52, 1, 0]]
  ![16, -17, -4] ![![289, 0, 0], ![-100, 14, 1]] where
    su := ![![36703, 0, 0], ![-15028, 289, 0]]
    hsu := by decide
    w := ![![4624, -4913, -1156], ![-2601, 5491, 289]]
    hw := by decide
    g := ![![![-16007107, 248604523, -25514816], ![17493923, 490419198, 0]], ![![6476273, -100580472, 10322787], ![-7077361, -198413874, 0]]]
    h := ![![![272, 45, -1], ![664, 123, 0]], ![![-127, 3, 0], ![-310, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {289} * I127N2 =  Ideal.span {B.equivFun.symm ![16, -17, -4]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E127RS2 


noncomputable def E137RS1 : RelationCertificate Table 17 ![![137, 0, 0], ![35, 1, 0]]
  ![4, -19, -2] ![![17, 0, 0], ![-2, 1, 0]] where
    su := ![![2329, 0, 0], ![595, 17, 0]]
    hsu := by decide
    w := ![![68, -323, -34], ![-34, 136, -17]]
    hw := by decide
    g := ![![![-95, -277, 137], ![8, -2364, 0]], ![![-24, -79, 39], ![6, -672, 0]]]
    h := ![![![22, -34, -1], ![-86, 135, 0]], ![![-46, -36, -1], ![180, 136, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {17} * I137N1 =  Ideal.span {B.equivFun.symm ![4, -19, -2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E137RS1 
