import IdealArithmetic.Examples.NF3_1_197127_1.PrimesBelow3_1_197127_1F1
import IdealArithmetic.Examples.NF3_1_197127_1.ClassGroupData3_1_197127_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 625 ![![37, 0, 0], ![0, 1, 0]]
  ![-229, -59, -16] ![![625, 0, 0], ![27, 1, 0]] where
    su := ![![23125, 0, 0], ![0, 625, 0]]
    hsu := by decide
    w := ![![-143125, -36875, -10000], ![-7500, -1875, -625]]
    hw := by decide
    g := ![![![331034475, -8607491678, -993172019], ![529278, 206910837288, 0]], ![![2751667, -71548723, -8255621], ![4783, 1719921042, 0]]]
    h := ![![![0, 4, -19], ![22, 229, 0]], ![![0, 0, -1], ![9, 12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {625} * I37N0 =  Ideal.span {B.equivFun.symm ![-229, -59, -16]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 5 ![![37, 0, 0], ![13, 1, 0]]
  ![-16, -1, 1] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![185, 0, 0], ![65, 5, 0]]
    hsu := by decide
    w := ![![-80, -5, 5], ![55, -10, 0]]
    hw := by decide
    g := ![![![-14838, 16422, 47678], ![-2649, -79464, 0]], ![![-5695, 6301, 18295], ![-1015, -30492, 0]]]
    h := ![![![1441, -17590, -4397], ![69, 54230, 0]], ![![-1019, 12240, 3060], ![-2, -37740, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {5} * I37N1 =  Ideal.span {B.equivFun.symm ![-16, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E37RS2 : RelationCertificate Table 5 ![![37, 0, 0], ![-13, 1, 0]]
  ![-11, -1, 1] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![185, 0, 0], ![-65, 5, 0]]
    hsu := by decide
    w := ![![-55, -5, 5], ![65, -5, 0]]
    hw := by decide
    g := ![![![-22569, 24989, 72548], ![-4028, -120913, 0]], ![![7751, -8585, -24921], ![1389, 41535, 0]]]
    h := ![![![888, 12174, -2609], ![53, 32178, 0]], ![![-1038, -14532, 3114], ![-1, -38406, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {5} * I37N2 =  Ideal.span {B.equivFun.symm ![-11, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS2 


noncomputable def E47RS1 : RelationCertificate Table 5 ![![47, 0, 0], ![9, 1, 0]]
  ![-37, -7, -3] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![235, 0, 0], ![45, 5, 0]]
    hsu := by decide
    w := ![![-185, -35, -15], ![-325, -65, -30]]
    hw := by decide
    g := ![![![6, -10, -33], ![6, 54, 0]], ![![2, -4, -12], ![1, 20, 0]]]
    h := ![![![203, -1705, -639], ![48, 10010, 0]], ![![363, -2993, -1122], ![50, 17576, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {5} * I47N1 =  Ideal.span {B.equivFun.symm ![-37, -7, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 3125 ![![53, 0, 0], ![-19, 1, 0]]
  ![-1846, -391, -159] ![![3125, 0, 0], ![-598, 1, 0]] where
    su := ![![165625, 0, 0], ![-59375, 3125, 0]]
    hsu := by decide
    w := ![![-5768750, -1221875, -496875], ![1090625, 231250, 93750]]
    hw := by decide
    g := ![![![-370884064144, -222146431911726, 1112586470526], ![-114482139, -1158944240131262, 0]], ![![139956250833, 83828842109265, -419843950533], ![43202979, 437337448471880, 0]]]
    h := ![![![19005, 378266, -56745], ![351, 1002442, 0]], ![![-3585, -71514, 10728], ![-44, -189518, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {3125} * I53N1 =  Ideal.span {B.equivFun.symm ![-1846, -391, -159]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E53RS1 


noncomputable def E59RS0 : RelationCertificate Table 3125 ![![59, 0, 0], ![13, 1, 0]]
  ![854, 59, 16] ![![3125, 0, 0], ![-598, 1, 0]] where
    su := ![![184375, 0, 0], ![40625, 3125, 0]]
    hsu := by decide
    w := ![![2668750, 184375, 50000], ![-509375, -34375, -9375]]
    hw := by decide
    g := ![![![24391809721, 14609830658807, -73171105148], ![7532077, 76219901195833, 0]], ![![5377051035, 3220663267533, -16130200007], ![1660218, 16802291673958, 0]]]
    h := ![![![132764264, -1598900538, -399716011], ![2153141, 7861081555, 0]], ![![-25341074, 305186357, 76294848], ![-410934, -1500465345, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {3125} * I59N0 =  Ideal.span {B.equivFun.symm ![854, 59, 16]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 25 ![![59, 0, 0], ![-10, 1, 0]]
  ![-49, -4, 4] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![1475, 0, 0], ![-250, 25, 0]]
    hsu := by decide
    w := ![![-1225, -100, 100], ![250, -25, 0]]
    hw := by decide
    g := ![![![-682005, 685263, 2052532], ![-27131, -17104432, 0]], ![![110237, -110765, -331767], ![4399, 2764725, 0]]]
    h := ![![![64705, 709672, -193552], ![1112, 3806524, 0]], ![![-13242, -145329, 39636], ![-178, -779508, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {25} * I59N1 =  Ideal.span {B.equivFun.symm ![-49, -4, 4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 3125 ![![59, 0, 0], ![-3, 1, 0]]
  ![-1417, 118, 32] ![![3125, 0, 0], ![-598, 1, 0]] where
    su := ![![184375, 0, 0], ![-9375, 3125, 0]]
    hsu := by decide
    w := ![![-4428125, 368750, 100000], ![850000, -71875, -18750]]
    hw := by decide
    g := ![![![15605678986510929, 9347249550138302579, -46814271544306090], ![4817125185857, 48764866191985510426, 0]], ![![-1058012086953773, -633711805322286597, 3173848775092456], ![-326584742306, -3306092474054641666, 0]]]
    h := ![![![25342, 101370, -76031], ![436, 1495287, 0]], ![![-4862, -19460, 14595], ![-31, -287037, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {3125} * I59N2 =  Ideal.span {B.equivFun.symm ![-1417, 118, 32]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E59RS2 


noncomputable def E67RS0 : RelationCertificate Table 25 ![![67, 0, 0], ![8, 1, 0]]
  ![13, -2, 2] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![1675, 0, 0], ![200, 25, 0]]
    hsu := by decide
    w := ![![325, -50, 50], ![200, 25, 0]]
    hw := by decide
    g := ![![![340, -340, -1019], ![15, 8491, 0]], ![![40, -43, -126], ![26, 1050, 0]]]
    h := ![![![-217, 1488, 638], ![38, -14248, 0]], ![![-130, 910, 390], ![1, -8710, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {25} * I67N0 =  Ideal.span {B.equivFun.symm ![13, -2, 2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 3125 ![![67, 0, 0], ![20, 1, 0]]
  ![4393, 878, 397] ![![3125, 0, 0], ![-598, 1, 0]] where
    su := ![![209375, 0, 0], ![62500, 3125, 0]]
    hsu := by decide
    w := ![![13728125, 2743750, 1240625], ![-2593750, -518750, -234375]]
    hw := by decide
    g := ![![![3891, 1979897, -9916], ![3062, 10329184, 0]], ![![1715, 685855, -3435], ![2979, 3578130, 0]]]
    h := ![![![776514599, -14814526157, -2339110529], ![10683077, 52240135280, 0]], ![![-146711950, 2799004585, 441943335], ![-2018401, -9870067840, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3125} * I67N1 =  Ideal.span {B.equivFun.symm ![4393, 878, 397]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 3125 ![![67, 0, 0], ![-28, 1, 0]]
  ![-153, 37, 63] ![![3125, 0, 0], ![-598, 1, 0]] where
    su := ![![209375, 0, 0], ![-87500, 3125, 0]]
    hsu := by decide
    w := ![![-478125, 115625, 196875], ![96875, -21875, -37500]]
    hw := by decide
    g := ![![![42820, 25355070, -126987], ![2566, 132278124, 0]], ![![-16610, -10015879, 50163], ![580, -52253124, 0]]]
    h := ![![![26550441, 765891643, -79230687], ![335512, 1769485364, 0]], ![![-5377927, -155135648, 16048620], ![-67927, -358419184, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {3125} * I67N2 =  Ideal.span {B.equivFun.symm ![-153, 37, 63]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E67RS2 


noncomputable def E79RS1 : RelationCertificate Table 5 ![![79, 0, 0], ![-32, 1, 0]]
  ![24, -6, 1] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![395, 0, 0], ![-160, 5, 0]]
    hsu := by decide
    w := ![![120, -30, 5], ![140, 25, -15]]
    hw := by decide
    g := ![![![84407, -93420, -271225], ![15083, 452046, 0]], ![![-33909, 37531, 108964], ![-6056, -181608, 0]]]
    h := ![![![-224, -7469, 679], ![5, -17880, 0]], ![![-240, -8614, 783], ![51, -20620, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {5} * I79N1 =  Ideal.span {B.equivFun.symm ![24, -6, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 
