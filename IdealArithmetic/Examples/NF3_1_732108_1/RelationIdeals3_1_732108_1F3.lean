import IdealArithmetic.Examples.NF3_1_732108_1.PrimesBelow3_1_732108_1F3
import IdealArithmetic.Examples.NF3_1_732108_1.ClassGroupData3_1_732108_1

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 75 ![![149, 0, 0], ![15, 1, 0]]
  ![-2098376, -27121, -64320] ![![75, 0, 0], ![5, 1, 1]] where
    su := ![![11175, 0, 0], ![1125, 75, 0]]
    hsu := by decide
    w := ![![-157378200, -2034075, -4824000], ![-13242075, -171150, -405900]]
    hw := by decide
    g := ![![![-348786623119096653, 260375307370030305, -39745267158197185], ![-20310707671781970, 750301436328916090, 27824754]], ![![-37119861496647719, 27710625081577053, -4229917990736048], ![-2161581338565283, 79851357681671132, 2961269]]]
    h := ![![![3128695453, -26711061545, -7855927085], ![135700511, 234106614269, 0]], ![![263253860, -2247515107, -661011348], ![11418165, 19698137088, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {75} * I149N1 =  Ideal.span {B.equivFun.symm ![-2098376, -27121, -64320]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E149RS1 


noncomputable def E167RS1 : RelationCertificate Table 15 ![![167, 0, 0], ![27, 1, 0]]
  ![-2059, 1856, 10] ![![15, 0, 0], ![-3, 1, 0]] where
    su := ![![2505, 0, 0], ![405, 15, 0]]
    hsu := by decide
    w := ![![-30885, 27840, 150], ![2835, -4245, 9240]]
    hw := by decide
    g := ![![![780900937167022, 411903763553031, -2016612259212846], ![-128719936529863, 6049836771676392, -7739214]], ![![131413749948883, 69317138205659, -339365169847694], ![-21661607442730, 1018095508539750, -1302392]]]
    h := ![![![-155830, 2286149, 394150], ![-11395, -13164608, 0]], ![![14362, -211104, -36392], ![1221, 1215616, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {15} * I167N1 =  Ideal.span {B.equivFun.symm ![-2059, 1856, 10]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 75 ![![173, 0, 0], ![7, 1, 0]]
  ![-4457, 3828, 1060] ![![75, 0, 0], ![5, 1, 1]] where
    su := ![![12975, 0, 0], ![525, 75, 0]]
    hsu := by decide
    w := ![![-334275, 287100, 79500], ![141375, -124125, -18825]]
    hw := by decide
    g := ![![![-241653042287, 180399569797, -27537228491], ![-14072038247, 519842075171, 346]], ![![-8380996969, 6256624022, -955046407], ![-488045411, 18029179795, 12]]]
    h := ![![![-66433737, 299131867, 166181285], ![-958922, -5749872249, 0]], ![![28102207, -126536119, -70296537], ![405762, 2432260130, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {75} * I173N1 =  Ideal.span {B.equivFun.symm ![-4457, 3828, 1060]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E173RS1 


noncomputable def E179RS1 : RelationCertificate Table 75 ![![179, 0, 0], ![86, 1, 0]]
  ![-2629, -34, -80] ![![75, 0, 0], ![27, 1, 0]] where
    su := ![![13425, 0, 0], ![6450, 75, 0]]
    hsu := by decide
    w := ![![-197175, -2550, -6000], ![-73875, -975, -2250]]
    hw := by decide
    g := ![![![343850412726621, -5266182640123550, -907839373860900], ![53570380046676, 13617590607905808, 1480]], ![![167276382659516, -2561893049593755, -441645788036554], ![26060923762918, 6624686820544568, 720]]]
    h := ![![![-51747, 2504548, 142300], ![-10798, -5094356, 0]], ![![-19429, 938369, 53315], ![-3960, -1908683, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {75} * I179N1 =  Ideal.span {B.equivFun.symm ![-2629, -34, -80]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E179RS1 


noncomputable def E181RS0 : RelationCertificate Table 25 ![![181, 0, 0], ![-74, 1, 0]]
  ![9, -11, 5] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![4525, 0, 0], ![-1850, 25, 0]]
    hsu := by decide
    w := ![![225, -275, 125], ![225, -200, -50]]
    hw := by decide
    g := ![![![54364, -110631, -140098], ![-62, 700264, 1068]], ![![-21890, 44542, 56407], ![46, -281944, -430]]]
    h := ![![![9541, 369226, -25640], ![-1749, 928169, 0]], ![![9413, 363926, -25272], ![-1702, 914846, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N0 : Ideal.span {25} * I181N0 =  Ideal.span {B.equivFun.symm ![9, -11, 5]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E181RS0 


noncomputable def E181RS1 : RelationCertificate Table 25 ![![181, 0, 0], ![-62, 1, 0]]
  ![-3682, 3503, -990] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![4525, 0, 0], ![-1550, 25, 0]]
    hsu := by decide
    w := ![![-92050, 87575, -24750], ![-51000, 43000, 16525]]
    hw := by decide
    g := ![![![1428367, 7615255, 9616639], ![418880, -47279466, -362]], ![![-436479, -2650019, -3345355], ![-140913, 16456385, 126]]]
    h := ![![![18849262, 597899495, -49823510], ![-3153252, 1803610864, 0]], ![![10432992, 330935124, -27577119], ![-1745324, 998291840, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {25} * I181N1 =  Ideal.span {B.equivFun.symm ![-3682, 3503, -990]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E181RS1 


noncomputable def E181RS2 : RelationCertificate Table 25 ![![181, 0, 0], ![-46, 1, 0]]
  ![72, -63, -10] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![4525, 0, 0], ![-1150, 25, 0]]
    hsu := by decide
    w := ![![1800, -1575, -250], ![-100, 150, -325]]
    hw := by decide
    g := ![![![427138906, -854275229, -1067843708], ![115, 5339218752, -181]], ![![-110906820, 221812995, 277266159], ![-24, -1386330848, 47]]]
    h := ![![![-207686, -4719193, 536255], ![26818, -19412433, 0]], ![![11664, 264914, -30103], ![-1484, 1089726, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N2 : Ideal.span {25} * I181N2 =  Ideal.span {B.equivFun.symm ![72, -63, -10]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E181RS2 


noncomputable def E191RS1 : RelationCertificate Table 15 ![![191, 0, 0], ![-33, 1, 0]]
  ![-417, 358, 100] ![![15, 0, 0], ![20, 1, 1]] where
    su := ![![2865, 0, 0], ![-495, 15, 0]]
    hsu := by decide
    w := ![![-6255, 5370, 1500], ![6990, -6255, -285]]
    hw := by decide
    g := ![![![5810081, -10087070, -7032156], ![6605496, 0, -7619836]], ![![-961299, 1668549, 1163214], ![-1092924, 0, 1260424]]]
    h := ![![![12347, 193915, -31275], ![-932, 1194725, 0]], ![![-13753, -216799, 34966], ![1337, -1335705, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {15} * I191N1 =  Ideal.span {B.equivFun.symm ![-417, 358, 100]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E191RS1 


noncomputable def E193RS0 : RelationCertificate Table 3 ![![193, 0, 0], ![5, 1, 0]]
  ![34973, 452, 1072] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![579, 0, 0], ![15, 3, 0]]
    hsu := by decide
    w := ![![104919, 1356, 3216], ![38760, 501, 1188]]
    hw := by decide
    g := ![![![-193, 169, 311], ![59, -193, 0]], ![![-7, 5, 8], ![4, -4, 0]]]
    h := ![![![23451213, -82096076, -58639376], ![182224, 2263480128, 0]], ![![8663531, -30328576, -21663018], ![67317, 836192574, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N0 : Ideal.span {3} * I193N0 =  Ideal.span {B.equivFun.symm ![34973, 452, 1072]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E193RS0 


noncomputable def E193RS1 : RelationCertificate Table 3 ![![193, 0, 0], ![56, 1, 0]]
  ![748, -695, 110] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![579, 0, 0], ![168, 3, 0]]
    hsu := by decide
    w := ![![2244, -2085, 330], ![5460, -4272, -3585]]
    hw := by decide
    g := ![![![11304499, -387594, -1094465], ![-129197, 854112, 0]], ![![3341989, -111999, -316380], ![-37333, 248248, 0]]]
    h := ![![![645478, -19448033, -1676515], ![86616, 64713501, 0]], ![![1569164, -47277464, -4075555], ![210456, 157316184, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {3} * I193N1 =  Ideal.span {B.equivFun.symm ![748, -695, 110]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E193RS1 


noncomputable def E193RS2 : RelationCertificate Table 3 ![![193, 0, 0], ![-62, 1, 0]]
  ![-570920, -7379, -17500] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![579, 0, 0], ![-186, 3, 0]]
    hsu := by decide
    w := ![![-1712760, -22137, -52500], ![-632742, -8178, -19395]]
    hw := by decide
    g := ![![![-45, 38, -400], ![13, 193, 0]], ![![-3, 1, 135], ![1, -63, 0]]]
    h := ![![![-83680266, -2637743217, 219806135], ![13214842, -8484520311, 0]], ![![-30913864, -974456971, 81202605], ![4881917, -3134421846, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N2 : Ideal.span {3} * I193N2 =  Ideal.span {B.equivFun.symm ![-570920, -7379, -17500]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E193RS2 
