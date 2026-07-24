import IdealArithmetic.Examples.NF3_1_623807_1.PrimesBelow3_1_623807_1F2
import IdealArithmetic.Examples.NF3_1_623807_1.ClassGroupData3_1_623807_1

set_option linter.all false

noncomputable section


noncomputable def E97RS0 : RelationCertificate Table 16 ![![97, 0, 0], ![-39, 1, 0]]
  ![14936, -3940, 601] ![![16, 0, 0], ![3, 0, 1]] where
    su := ![![1552, 0, 0], ![-624, 16, 0]]
    hsu := by decide
    w := ![![238976, -63040, 9616], ![-645424, 33856, 21280]]
    hw := by decide
    g := ![![![2278471, 407186, 77645], ![432069, -1020, 0]], ![![-19882867, -525954, 327181], ![-3707587, 2083933, 0]]]
    h := ![![![118796, -3174, 11], ![295084, -233, 0]], ![![-320086, 8517, -2], ![-795077, 762, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {16} * I97N0 =  Ideal.span {B.equivFun.symm ![14936, -3940, 601]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 8 ![![97, 0, 0], ![-29, 1, 0]]
  ![-241285728, 34481172, 395155] ![![8, 0, 0], ![3, 0, 1]] where
    su := ![![776, 0, 0], ![-232, 8, 0]]
    hsu := by decide
    w := ![![-1930285824, 275849376, 3161240], ![4457217400, 133475296, -274186280]]
    hw := by decide
    g := ![![![-751782713417818, -148546995652090, -2933057662523], ![-282285149739497, 434280, 0]], ![![551137460840649, 42548493358233, -19607670996358], ![204225588940701, -22694917343473, 0]]]
    h := ![![![-58180856950, 2152977070, -10458135], ![-194596615118, 507417125, 0]], ![![134230276145, -4966553874, 23810505], ![448957918410, -1171946135, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {8} * I97N1 =  Ideal.span {B.equivFun.symm ![-241285728, 34481172, 395155]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E97RS1 


noncomputable def E101RS0 : RelationCertificate Table 2 ![![101, 0, 0], ![8, 1, 0]]
  ![-4510, 432, 81] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![202, 0, 0], ![16, 2, 0]]
    hsu := by decide
    w := ![![-9020, 864, 162], ![48842, 6588, -4780]]
    hw := by decide
    g := ![![![3097769, 649647, -485840], ![1305967, 0, 0]], ![![453308, 95027, -71105], ![191104, -3, 0]]]
    h := ![![![-12550, -1576, -3], ![157880, 192, 0]], ![![67953, 8567, -8], ![-854854, -791, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {2} * I101N0 =  Ideal.span {B.equivFun.symm ![-4510, 432, 81]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![12, 1, 0]]
  ![-2047979514, 119684188, 63277293] ![![2, 0, 0], ![1, 0, 1]] where
    su := ![![202, 0, 0], ![24, 2, 0]]
    hsu := by decide
    w := ![![-4095959028, 239368376, 126554586], ![6525868526, 4928758456, -2041109116]]
    hw := by decide
    g := ![![![-663005178160359681, -139041745028599354, 103982510308726311], ![-279511333925816683, 0, 0]], ![![-123237065266206450, -25844589410842173, 19327902453215933], ![-51954581406495256, -3, 0]]]
    h := ![![![-32776212474, -2781349576, -7507843], ![275695790030, 410784718, 0]], ![![52356054059, 4468546786, 2793142], ![-440391543808, -651330950, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![-2047979514, 119684188, 63277293]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 8 ![![101, 0, 0], ![-20, 1, 0]]
  ![3416992, -687348, 63353] ![![8, 0, 0], ![3, 0, 1]] where
    su := ![![808, 0, 0], ![-160, 8, 0]]
    hsu := by decide
    w := ![![27335936, -5498784, 506824], ![-103855576, 2752784, 4357752]]
    hw := by decide
    g := ![![![56922630042723717, 1278598608125360, -3046869730875314], ![20965127549661985, -3409728358719562, 0]], ![![-11553621177854847, -259521105918294, 618423983857542], ![-4255304943713372, 692073577753611, 0]]]
    h := ![![![133472, 53481100, -5630203], ![503184, 284356928, 0]], ![![-494187, -196385887, 20679875], ![-1846547, -1044061328, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {8} * I101N2 =  Ideal.span {B.equivFun.symm ![3416992, -687348, 63353]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E101RS2 


noncomputable def E109RS0 : RelationCertificate Table 8 ![![109, 0, 0], ![20, 1, 0]]
  ![12096, -276, -523] ![![8, 0, 0], ![3, 0, 1]] where
    su := ![![872, 0, 0], ![160, 8, 0]]
    hsu := by decide
    w := ![![96768, -2208, -4184], ![73832, -40576, 10280]]
    hw := by decide
    g := ![![![6674554, 483109, -248010], ![2471961, -285852, 0]], ![![268873565802, 6039738988, -14391768805], ![99028616084, -16105724407, 0]]]
    h := ![![![1814864, 93988, 305], ![-9890404, -16884, 0]], ![![1384621, 71671, 249], ![-7545723, -12928, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {8} * I109N0 =  Ideal.span {B.equivFun.symm ![12096, -276, -523]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 16 ![![109, 0, 0], ![-40, 1, 0]]
  ![27774456920, 4810659340, 1237703613] ![![16, 0, 0], ![3, 0, 1]] where
    su := ![![1744, 0, 0], ![-640, 16, 0]]
    hsu := by decide
    w := ![![444391310720, 76970549440, 19803257808], ![626412641264, 108497452608, 27914612032]]
    hw := by decide
    g := ![![![91832106, 1880729, -1690761], ![17112851, -10016100, 0]], ![![229457365595085063, 4686998688017070, -4234744428651097], ![42758584522287768, -24997326336101701, 0]]]
    h := ![![![371044491560, -10097850740, 56085501], ![1010401878078, -2437807998, 0]], ![![523023187851, -14233899724, 79057952], ![1424259417142, -3436326758, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {16} * I109N1 =  Ideal.span {B.equivFun.symm ![27774456920, 4810659340, 1237703613]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E109RS1 


noncomputable def E127RS0 : RelationCertificate Table 16 ![![127, 0, 0], ![55, 1, 0]]
  ![-360, 108, -19] ![![16, 0, 0], ![3, 0, 1]] where
    su := ![![2032, 0, 0], ![880, 16, 0]]
    hsu := by decide
    w := ![![-5760, 1728, -304], ![18224, -1120, -544]]
    hw := by decide
    g := ![![![-877795691, -17929970, 16200227], ![-163574171, 95628174, 0]], ![![-376691786, -7694340, 6952070], ![-70195203, 41037291, 0]]]
    h := ![![![-134920, -3428, -35], ![311536, 2213, 0]], ![![428187, 10704, 104], ![-988702, -6621, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {16} * I127N0 =  Ideal.span {B.equivFun.symm ![-360, 108, -19]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 16 ![![127, 0, 0], ![-44, 1, 0]]
  ![-8, -4, 1] ![![16, 0, 0], ![3, 0, 1]] where
    su := ![![2032, 0, 0], ![-704, 16, 0]]
    hsu := by decide
    w := ![![-128, -64, 16], ![-784, 64, 0]]
    hw := by decide
    g := ![![![-90415179, -1846861, 1668654], ![-16848543, 9849924, 0]], ![![-161434932, -3297542, 2979358], ![-30082836, 17586891, 0]]]
    h := ![![![-2656, 82, -1], ![-7666, 64, 0]], ![![-16455, 417, -2], ![-47494, 127, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {16} * I127N1 =  Ideal.span {B.equivFun.symm ![-8, -4, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 4 ![![127, 0, 0], ![-11, 1, 0]]
  ![28, 4, 1] ![![4, 0, 0], ![-1, 0, 1]] where
    su := ![![508, 0, 0], ![-44, 4, 0]]
    hsu := by decide
    w := ![![112, 16, 4], ![428, 72, 24]]
    hw := by decide
    g := ![![![9129, -65, 476], ![-2159, -254, 0]], ![![-826, 6, -44], ![199, 23, 0]]]
    h := ![![![1222, -106, -1], ![14106, 64, 0]], ![![4636, -421, 0], ![53515, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {4} * I127N2 =  Ideal.span {B.equivFun.symm ![28, 4, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E127RS2 
