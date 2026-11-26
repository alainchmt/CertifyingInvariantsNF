import IdealArithmetic.Examples.NF3_1_780332_1.PrimesBelow3_1_780332_1F2
import IdealArithmetic.Examples.NF3_1_780332_1.ClassGroupData3_1_780332_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 59049 ![![83, 0, 0], ![35, 1, 0]]
  ![3285, 559, 16] ![![59049, 0, 0], ![-504, 5, 1]] where
    su := ![![4901067, 0, 0], ![2066715, 59049, 0]]
    hsu := by decide
    w := ![![193975965, 33008391, 944784], ![-1299078, -177147, 0]]
    hw := by decide
    g := ![![![-287638846763, 195897243108, -2577639916], ![2471680597, 30440917543920, 0]], ![![-136898535773, 93235131551, -1226799279], ![1176353125, 14488018854530, 0]]]
    h := ![![![22020, 733, 3], ![-52125, -233, 0]], ![![-174, -40, -1], ![412, 83, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {59049} * I83N1 =  Ideal.span {B.equivFun.symm ![3285, 559, 16]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E83RS1 


noncomputable def E89RS0 : RelationCertificate Table 81 ![![89, 0, 0], ![16, 1, 0]]
  ![27, 17, 2] ![![81, 0, 0], ![-63, -4, 1]] where
    su := ![![7209, 0, 0], ![1296, 81, 0]]
    hsu := by decide
    w := ![![2187, 1377, 162], ![3321, 1053, 81]]
    hw := by decide
    g := ![![![22483221, 3086581, -41745], ![-17639804, -5255280, 0]], ![![5551449, 762121, -10308], ![-4355455, -1297600, 0]]]
    h := ![![![131, 8, 0], ![-727, 2, 0]], ![![225, 14, 0], ![-1249, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {81} * I89N0 =  Ideal.span {B.equivFun.symm ![27, 17, 2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E89RS0 


noncomputable def E89RS1 : RelationCertificate Table 9 ![![89, 0, 0], ![25, 1, 0]]
  ![141, 2, -1] ![![9, 0, 0], ![165, 14, -2]] where
    su := ![![801, 0, 0], ![225, 9, 0]]
    hsu := by decide
    w := ![![1269, 18, -9], ![13221, 1188, -171]]
    hw := by decide
    g := ![![![151287, -402154, -18615], ![2152498, 319466, 0]], ![![45364, -120961, -5597], ![647375, 96080, 0]]]
    h := ![![![20294, 887, 3], ![-72241, -268, 0]], ![![211646, 9372, 36], ![-753401, -3223, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {9} * I89N1 =  Ideal.span {B.equivFun.symm ![141, 2, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 729 ![![89, 0, 0], ![-41, 1, 0]]
  ![11565, 1019, -148] ![![729, 0, 0], ![12834, 725, -152]] where
    su := ![![64881, 0, 0], ![-29889, 729, 0]]
    hsu := by decide
    w := ![![8430885, 742851, -107892], ![2124306, 1503927, -129033]]
    hw := by decide
    g := ![![![357841523, 2138609519, 480050362], ![8326700834, 1263036985, 0]], ![![-161810209, -966972538, -217054526], ![-3764915354, -571081910, 0]]]
    h := ![![![383700773, -10834035, 35986], ![832911152, -3202902, 0]], ![![96219146, -2718572, 9066], ![208865880, -807051, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {729} * I89N2 =  Ideal.span {B.equivFun.symm ![11565, 1019, -148]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E89RS2 


noncomputable def E103RS1 : RelationCertificate Table 9 ![![103, 0, 0], ![-28, 1, 0]]
  ![-1485, 89, 2] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![927, 0, 0], ![-252, 9, 0]]
    hsu := by decide
    w := ![![-13365, 801, 18], ![7056, -1593, 81]]
    hw := by decide
    g := ![![![-95497, -2203703, 556005], ![-202406, -5005200, 0]], ![![24146, 569080, -143649], ![52505, 1293010, 0]]]
    h := ![![![-389875, 14849, -33], ![-1434130, 3401, 0]], ![![206024, -7833, 17], ![757846, -1742, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {9} * I103N1 =  Ideal.span {B.equivFun.symm ![-1485, 89, 2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 177147 ![![107, 0, 0], ![38, 1, 0]]
  ![-72963, -5072, 829] ![![177147, 0, 0], ![-13545, 167, 1]] where
    su := ![![18954729, 0, 0], ![6731586, 177147, 0]]
    hsu := by decide
    w := ![![-12925176561, -898489584, 146854863], ![1062704853, 73516005, -12045996]]
    hw := by decide
    g := ![![![-702653227071, 17028455753842, -211889455547], ![69778185262, 224763542536530, 0]], ![![-263808134128, 6393260745536, -79552988137], ![26198039650, 84386508930935, 0]]]
    h := ![![![-657367, -19713, -55], ![1849087, 6714, 0]], ![![54015, 1600, 4], ![-151937, -496, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {177147} * I107N0 =  Ideal.span {B.equivFun.symm ![-72963, -5072, 829]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 3 ![![107, 0, 0], ![-21, 1, 0]]
  ![-2283, -82, 20] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![321, 0, 0], ![-63, 3, 0]]
    hsu := by decide
    w := ![![-6849, -246, 60], ![13443, 279, -102]]
    hw := by decide
    g := ![![![-7223, 47914, -58350], ![18382, 174122, 0]], ![![-48, -9546, 10926], ![-3165, -32708, 0]]]
    h := ![![![-27360, 1347, -2], ![-139297, 234, 0]], ![![53764, -2627, 3], ![273727, -355, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {3} * I107N1 =  Ideal.span {B.equivFun.symm ![-2283, -82, 20]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 27 ![![107, 0, 0], ![-17, 1, 0]]
  ![-38151, -11429, -884] ![![27, 0, 0], ![-402, -32, 5]] where
    su := ![![2889, 0, 0], ![-459, 27, 0]]
    hsu := by decide
    w := ![![-1030077, -308583, -23868], ![-765504, -229338, -17739]]
    hw := by decide
    g := ![![![-177, 57, -38], ![2777, 388, 0]], ![![397, 20, 1], ![-383, -56, 0]]]
    h := ![![![-19427604, 1167658, -1478], ![-122277381, 157262, 0]], ![![-14437664, 867741, -1098], ![-90870688, 116829, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {27} * I107N2 =  Ideal.span {B.equivFun.symm ![-38151, -11429, -884]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E107RS2 


noncomputable def E113RS1 : RelationCertificate Table 81 ![![113, 0, 0], ![-51, 1, 0]]
  ![1611, 481, 37] ![![81, 0, 0], ![-3180, -266, 38]] where
    su := ![![9153, 0, 0], ![-4131, 81, 0]]
    hsu := by decide
    w := ![![130491, 38961, 2997], ![-415692, -127494, -10044]]
    hw := by decide
    g := ![![![181, 3547, 182], ![7895, 1183, 0]], ![![1233, -1360, -91], ![-3237, -490, 0]]]
    h := ![![![7983807, -178505, 431], ![17689580, -48666, 0]], ![![-25431802, 568768, -1376], ![-56348794, 155364, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {81} * I113N1 =  Ideal.span {B.equivFun.symm ![1611, 481, 37]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E113RS1 


noncomputable def E127RS1 : RelationCertificate Table 243 ![![127, 0, 0], ![13, 1, 0]]
  ![1143, 338, 26] ![![243, 0, 0], ![-144, -4, 1]] where
    su := ![![30861, 0, 0], ![3159, 243, 0]]
    hsu := by decide
    w := ![![277749, 82134, 6318], ![-34020, -9720, -729]]
    hw := by decide
    g := ![![![-10745, 630, 78], ![6532, 6365, 0]], ![![-1103, 65, 8], ![676, 655, 0]]]
    h := ![![![3101653, 241461, 221], ![-30300676, -28041, 0]], ![![-379900, -29587, -28], ![3711320, 3553, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {243} * I127N1 =  Ideal.span {B.equivFun.symm ![1143, 338, 26]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS1 


noncomputable def E137RS1 : RelationCertificate Table 531441 ![![137, 0, 0], ![30, 1, 0]]
  ![-4149, 572, 152] ![![531441, 0, 0], ![163602, 167, 1]] where
    su := ![![72807417, 0, 0], ![15943230, 531441, 0]]
    hsu := by decide
    w := ![![-2204948709, 303984252, 80779032], ![-664301250, 96190821, 24977727]]
    hw := by decide
    g := ![![![13040971671261, 4311430137329407, 4397636664289], ![5369443487579, -13994549676346700, 0]], ![![2968045483248, 981255185939004, 1000875265343], ![1222052820897, -3185074095460900, 0]]]
    h := ![![![-26277, -934, -1], ![119860, 289, 0]], ![![-7930, -303, -1], ![36172, 184, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {531441} * I137N1 =  Ideal.span {B.equivFun.symm ![-4149, 572, 152]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E137RS1 
