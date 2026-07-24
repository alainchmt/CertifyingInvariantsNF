import IdealArithmetic.Examples.NF3_1_780300_1.PrimesBelow3_1_780300_1F2
import IdealArithmetic.Examples.NF3_1_780300_1.ClassGroupData3_1_780300_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 396 ![![83, 0, 0], ![26, 1, 0]]
  ![32, -16, 7] ![![396, 0, 0], ![12, 6, 0]] where
    su := ![![32868, 0, 0], ![10296, 396, 0]]
    hsu := by decide
    w := ![![12672, -6336, 2772], ![7524, 0, -396]]
    hw := by decide
    g := ![![![56499, -123160562, -307972024], ![-1864315, 4065230720, 0]], ![![-88809806, 193605380119, 484124462557], ![2930723662, -6390442905751, 0]]]
    h := ![![![100, -2, -1], ![-318, 18, 0]], ![![61, -8, -2], ![-194, 33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {396} * I83N1 =  Ideal.span {B.equivFun.symm ![32, -16, 7]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 484 ![![89, 0, 0], ![42, 1, 0]]
  ![106, -42, 17] ![![484, 0, 0], ![224, 2, 0]] where
    su := ![![43076, 0, 0], ![20328, 484, 0]]
    hsu := by decide
    w := ![![51304, -20328, 8228], ![29524, -9196, 3388]]
    hw := by decide
    g := ![![![-25021355021526, 15885879579152269, 709201026076242], ![54063999242945, -34325329662090107, 0]], ![![-11526692088795, 7318214473601811, 326710597789976], ![24905888263292, -15812792933034835, 0]]]
    h := ![![![1155962, 36828, 1108], ![-2449536, -19719, 0]], ![![666149, 21219, 638], ![-1411600, -11355, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {484} * I89N1 =  Ideal.span {B.equivFun.symm ![106, -42, 17]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 2108304 ![![101, 0, 0], ![-15, 1, 0]]
  ![-10106, 598, 23] ![![2108304, 0, 0], ![-3120, 24, 0]] where
    su := ![![212938704, 0, 0], ![-31624560, 2108304, 0]]
    hsu := by decide
    w := ![![-21306520224, 1260765792, 48490992], ![31624560, -2108304, 0]]
    hw := by decide
    g := ![![![52004159, 3087016388432916, -118731399570498], ![35141210405, 2086015705333993457, 0]], ![![-8238230, -489032299522849, 18808934599470], ![-5566888867, -330457933765008324, 0]]]
    h := ![![![-49246, 3349, -22], ![-330916, 449, 0]], ![![90, -6, 0], ![605, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2108304} * I101N1 =  Ideal.span {B.equivFun.symm ![-10106, 598, 23]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 95832 ![![107, 0, 0], ![43, 1, 0]]
  ![3286, 271, 164] ![![95832, 0, 0], ![-40560, 0, 12]] where
    su := ![![10254024, 0, 0], ![4120776, 95832, 0]]
    hsu := by decide
    w := ![![314903952, 25970472, 15716448], ![-132727320, -10924848, -6612408]]
    hw := by decide
    g := ![![![-111032321356368, 2603034166040771, -5884472011], ![46993393479803, 6150245813609940, 0]], ![![-45347252848197, 1063117901726045, -2403305965], ![19192801436473, 2511851941770472, 0]]]
    h := ![![![6414, 155, 2], ![-15884, -10, 0]], ![![-2734, -76, -2], ![6771, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {95832} * I107N1 =  Ideal.span {B.equivFun.symm ![3286, 271, 164]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E107RS1 


noncomputable def E113RS1 : RelationCertificate Table 4356 ![![113, 0, 0], ![17, 1, 0]]
  ![113, 26, 1] ![![4356, 0, 0], ![-1560, 12, 0]] where
    su := ![![492228, 0, 0], ![74052, 4356, 0]]
    hsu := by decide
    w := ![![492228, 113256, 4356], ![-174240, -39204, 0]]
    hw := by decide
    g := ![![![731, 738317, -28397], ![2041, 2061624, 0]], ![![139, 118377, -4553], ![388, 330548, 0]]]
    h := ![![![307, 8, -3], ![-2034, 68, 0]], ![![-118, -24, -5], ![782, 113, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {4356} * I113N1 =  Ideal.span {B.equivFun.symm ![113, 26, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 1452 ![![131, 0, 0], ![-4, 1, 0]]
  ![-526, -45, -25] ![![1452, 0, 0], ![-20, 4, 2]] where
    su := ![![190212, 0, 0], ![-5808, 1452, 0]]
    hsu := by decide
    w := ![![-763752, -65340, -36300], ![-21780, -2904, -1452]]
    hw := by decide
    g := ![![![-76541, 4500, -4505], ![1225, 326943, 0]], ![![2134, -126, 125], ![240, -9099, 0]]]
    h := ![![![-554, 141, -5], ![-18012, 126, 0]], ![![-9, 3, -1], ![-291, 26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {1452} * I131N1 =  Ideal.span {B.equivFun.symm ![-526, -45, -25]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 2108304 ![![137, 0, 0], ![61, 1, 0]]
  ![-10072, 1274, 49] ![![2108304, 0, 0], ![-3120, 24, 0]] where
    su := ![![288837648, 0, 0], ![128606544, 2108304, 0]]
    hsu := by decide
    w := ![![-21234837888, 2685979296, 103306896], ![31624560, -4216608, 0]]
    hw := by decide
    g := ![![![4, -393747198, 15144123], ![2695, -266070125792, 0]], ![![2, -175143774, 6736299], ![1347, -118351384381, 0]]]
    h := ![![![-38524, -784, -13], ![86356, 366, 0]], ![![-60, -1, 0], ![135, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {2108304} * I137N1 =  Ideal.span {B.equivFun.symm ![-10072, 1274, 49]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E137RS1 
