import IdealArithmetic.Examples.NF3_1_399916_3.PrimesBelow3_1_399916_3F3
import IdealArithmetic.Examples.NF3_1_399916_3.ClassGroupData3_1_399916_3

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 11 ![![139, 0, 0], ![-61, 1, 0]]
  ![-1821, -756, 317] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![1529, 0, 0], ![-671, 11, 0]]
    hsu := by decide
    w := ![![-20031, -8316, 3487], ![34276, -3333, -561]]
    hw := by decide
    g := ![![![788852, 1222171, 1222989], ![254538, -6659136, 0]], ![![-320135, -502435, -503150], ![-103876, 2741008, 0]]]
    h := ![![![5438, -486461, 15953], ![-5752, -1108575, 0]], ![![-9336, 842903, -27639], ![10165, 1920885, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {11} * I139N1 =  Ideal.span {B.equivFun.symm ![-1821, -756, 317]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS1 


noncomputable def E157RS0 : RelationCertificate Table 11 ![![157, 0, 0], ![7, 1, 0]]
  ![145, -12, -3] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![1727, 0, 0], ![77, 11, 0]]
    hsu := by decide
    w := ![![1595, -132, -33], ![-88, 121, -33]]
    hw := by decide
    g := ![![![-344, -945, -969], ![-138, 5364, 0]], ![![-13, -45, -46], ![0, 256, 0]]]
    h := ![![![-2577, -18070, -5163], ![-80, 405294, 0]], ![![142, 1025, 293], ![100, -23002, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N0 : Ideal.span {11} * I157N0 =  Ideal.span {B.equivFun.symm ![145, -12, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E157RS0 


noncomputable def E157RS2 : RelationCertificate Table 121 ![![157, 0, 0], ![75, 1, 0]]
  ![75162724, 11305641, 4003237] ![![121, 0, 0], ![-31, 1, 0]] where
    su := ![![18997, 0, 0], ![9075, 121, 0]]
    hsu := by decide
    w := ![![9094689604, 1367982561, 484391677], ![-1830343889, -275312147, -97485828]]
    hw := by decide
    g := ![![![-289345113, 10228498954, -659987781], ![158662846, 39929258536, 0]], ![![-140000356, 4949083740, -319336668], ![76769381, 19319867480, 0]]]
    h := ![![![1186961586, 141607537983, 3776474099], ![1468978785, -296451215153, 0]], ![![-238880939, -28499102561, -760031028], ![-295638030, 59662032864, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N2 : Ideal.span {121} * I157N2 =  Ideal.span {B.equivFun.symm ![75162724, 11305641, 4003237]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E157RS2 


noncomputable def E173RS0 : RelationCertificate Table 121 ![![173, 0, 0], ![-79, 1, 0]]
  ![2216, 333, 119] ![![121, 0, 0], ![-31, 1, 0]] where
    su := ![![20933, 0, 0], ![-9559, 121, 0]]
    hsu := by decide
    w := ![![268136, 40293, 14399], ![-53845, -8107, -2904]]
    hw := by decide
    g := ![![![-361448610, 12777410893, -824454769], ![198201036, 49879513515, 0]], ![![163352096, -5774587770, 372601810], ![-89574389, -22542409500, 0]]]
    h := ![![![22253342, -2684181289, 67957715], ![-25677422, -5878342288, 0]], ![![-4468674, 539015312, -13646712], ![5156461, 1180440576, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N0 : Ideal.span {121} * I173N0 =  Ideal.span {B.equivFun.symm ![2216, 333, 119]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E173RS0 


noncomputable def E173RS2 : RelationCertificate Table 11 ![![173, 0, 0], ![-27, 1, 0]]
  ![-435, 608, -167] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![1903, 0, 0], ![-297, 11, 0]]
    hsu := by decide
    w := ![![-4785, 6688, -1837], ![-20636, 781, 715]]
    hw := by decide
    g := ![![![85456, 13284, 6287], ![16751, -8890, 0]], ![![-10080, -1617, -794], ![-1972, 1345, 0]]]
    h := ![![![3530, -99755, 7389], ![-1041, -639232, 0]], ![![14573, -412704, 30573], ![-4501, -2644532, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N2 : Ideal.span {11} * I173N2 =  Ideal.span {B.equivFun.symm ![-435, 608, -167]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E173RS2 
