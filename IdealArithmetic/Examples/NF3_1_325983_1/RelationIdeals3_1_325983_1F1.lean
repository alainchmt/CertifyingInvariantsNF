import IdealArithmetic.Examples.NF3_1_325983_1.PrimesBelow3_1_325983_1F1
import IdealArithmetic.Examples.NF3_1_325983_1.ClassGroupData3_1_325983_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 19683 ![![37, 0, 0], ![-7, 1, 0]]
  ![4189, 327, 293] ![![19683, 0, 0], ![-543, 1, 0]] where
    su := ![![728271, 0, 0], ![-137781, 19683, 0]]
    hsu := by decide
    w := ![![82452087, 6436341, 5767119], ![-2243862, -177147, -157464]]
    hw := by decide
    g := ![![![1855322389066324, 1324745759071205858907, -12220901867970533568], ![67252874003669347, 48108802293452802443793, 0]], ![![-367721554486258, -262562222445145600393, 2422160729910970478], ![-13329398447427286, -9535077929367526383695, 0]]]
    h := ![![![102129515, -14589949, 44], ![539826838, -267, 0]], ![![-2779246, 397039, -4], ![-14690284, 28, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {19683} * I37N1 =  Ideal.span {B.equivFun.symm ![4189, 327, 293]} * (J0 ^ 9) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9 E37RS1 


noncomputable def E41RS0 : RelationCertificate Table 2187 ![![41, 0, 0], ![5, 1, 0]]
  ![617, -3, 4] ![![2187, 0, 0], ![-543, 1, 0]] where
    su := ![![89667, 0, 0], ![10935, 2187, 0]]
    hsu := by decide
    w := ![![1349379, -6561, 8748], ![-334611, 2187, -2187]]
    hw := by decide
    g := ![![![115025944, 1075650258979, -9922974823], ![463281288, 4340309187580, 0]], ![![22732153, 212573723976, -1961012600], ![91556572, 857746911240, 0]]]
    h := ![![![-48, 20848, 17384], ![517, -142548, 0]], ![![7, -5171, -4311], ![-88, 35350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {2187} * I41N0 =  Ideal.span {B.equivFun.symm ![617, -3, 4]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 81 ![![41, 0, 0], ![11, 1, 0]]
  ![-50, 3, -4] ![![81, 0, 0], ![24, 1, 0]] where
    su := ![![3321, 0, 0], ![891, 81, 0]]
    hsu := by decide
    w := ![![-4050, 243, -324], ![-1620, 81, -81]]
    hw := by decide
    g := ![![![0, -205, -41], ![-1, 664, 0]], ![![-1, -105, -21], ![3, 340, 0]]]
    h := ![![![8670, 779, -4], ![-32320, 32, 0]], ![![3468, 313, -1], ![-12928, 8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {81} * I41N1 =  Ideal.span {B.equivFun.symm ![-50, 3, -4]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 81 ![![41, 0, 0], ![-17, 1, 0]]
  ![437, 24, 22] ![![81, 0, 0], ![24, 1, 0]] where
    su := ![![3321, 0, 0], ![-1377, 81, 0]]
    hsu := by decide
    w := ![![35397, 1944, 1782], ![12798, 729, 648]]
    hw := by decide
    g := ![![![-7, 1570, 314], ![26, -5088, 0]], ![![-27431, 8151617, 1630552], ![92578, -26414942, 0]]]
    h := ![![![332, 36649, -11458], ![775, 93960, 0]], ![![127, 13248, -4142], ![297, 33966, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {81} * I41N2 =  Ideal.span {B.equivFun.symm ![437, 24, 22]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E41RS2 


noncomputable def E43RS0 : RelationCertificate Table 81 ![![43, 0, 0], ![-17, 1, 0]]
  ![178, 12, 11] ![![81, 0, 0], ![24, 1, 0]] where
    su := ![![3483, 0, 0], ![-1377, 81, 0]]
    hsu := by decide
    w := ![![14418, 972, 891], ![5427, 324, 324]]
    hw := by decide
    g := ![![![-44, 10468, 2094], ![147, -33922, 0]], ![![0, -4105, -821], ![1, 13300, 0]]]
    h := ![![![262836, -17178, 537], ![664810, -4616, 0]], ![![98955, -6470, 203], ![250294, -1745, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {81} * I43N0 =  Ideal.span {B.equivFun.symm ![178, 12, 11]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 2187 ![![43, 0, 0], ![-10, 1, 0]]
  ![226, -33, 44] ![![2187, 0, 0], ![-543, 1, 0]] where
    su := ![![94041, 0, 0], ![-21870, 2187, 0]]
    hsu := by decide
    w := ![![494262, -72171, 96228], ![-118098, 17496, -24057]]
    hw := by decide
    g := ![![![295712563, 2765326047613, -25510392917], ![1191019107, 11158245861898, 0]], ![![-59601310, -557356883007, 5141669675], ![-240051685, -2248966315845, 0]]]
    h := ![![![1375802, -137575, -2], ![5915926, 26, 0]], ![![-328738, 32877, -2], ![-1413568, 15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {2187} * I43N1 =  Ideal.span {B.equivFun.symm ![226, -33, 44]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 177147 ![![53, 0, 0], ![22, 1, 0]]
  ![-14902, 1905, 1105] ![![177147, 0, 0], ![58506, 1, 0]] where
    su := ![![9388791, 0, 0], ![3897234, 177147, 0]]
    hsu := by decide
    w := ![![-2639844594, 337465035, 195747435], ![-871740387, 111425463, 64658655]]
    hw := by decide
    g := ![![![-7800357997295, 4640271915094908211, 396556985935720], ![23618261685072, -14049776077510998112, 0]], ![![-3338426570352, 1985961031908818309, 169719950772205], ![10108232517317, -6013076023888759798, 0]]]
    h := ![![![-24720806590, -1538920088, -90271090], ![59554669744, 956873775, 0]], ![![-8163411067, -508188752, -29809695], ![19666399165, 315982840, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {177147} * I53N1 =  Ideal.span {B.equivFun.symm ![-14902, 1905, 1105]} * (J0 ^ 11) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11 E53RS1 


noncomputable def E59RS0 : RelationCertificate Table 3 ![![59, 0, 0], ![4, 1, 0]]
  ![-4, 0, 1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![177, 0, 0], ![12, 3, 0]]
    hsu := by decide
    w := ![![-12, 0, 3], ![105, -18, 0]]
    hw := by decide
    g := ![![![36, 2, 2], ![1, 0, 0]], ![![6, 0, 2], ![2, -1, 0]]]
    h := ![![![-4, -2, -1], ![58, 12, 0]], ![![29, 7, 0], ![-419, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {3} * I59N0 =  Ideal.span {B.equivFun.symm ![-4, 0, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 81 ![![59, 0, 0], ![20, 1, 0]]
  ![-103, 24, -5] ![![81, 0, 0], ![24, 1, 0]] where
    su := ![![4779, 0, 0], ![1620, 81, 0]]
    hsu := by decide
    w := ![![-8343, 1944, -405], ![-2997, 567, 0]]
    hw := by decide
    g := ![![![1103497, -328150998, -65639395], ![-3724275, 1063358206, 0]], ![![389253, -115754757, -23154195], ![-1313717, 375097962, 0]]]
    h := ![![![5703, 265, -5], ![-16829, 58, 0]], ![![1997, 79, -5], ![-5893, 59, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {81} * I59N1 =  Ideal.span {B.equivFun.symm ![-103, 24, -5]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 59049 ![![59, 0, 0], ![-25, 1, 0]]
  ![5849, 762, 442] ![![59049, 0, 0], ![-543, 1, 0]] where
    su := ![![3483891, 0, 0], ![-1476225, 59049, 0]]
    hsu := by decide
    w := ![![345377601, 44995338, 26099658], ![-3129597, -413343, -236196]]
    hw := by decide
    g := ![![![263, 53134536, -490171], ![28600, 5788821485, 0]], ![![523, -21983521, 202800], ![56874, -2395027444, 0]]]
    h := ![![![3317048461, -132682284, 83], ![7828234134, -891, 0]], ![![-30055367, 1202219, -1], ![-70930664, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {59049} * I59N2 =  Ideal.span {B.equivFun.symm ![5849, 762, 442]} * (J0 ^ 10) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10 E59RS2 


noncomputable def E67RS0 : RelationCertificate Table 9 ![![67, 0, 0], ![7, 1, 0]]
  ![8, -3, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![603, 0, 0], ![63, 9, 0]]
    hsu := by decide
    w := ![![72, -27, 9], ![81, 0, -18]]
    hw := by decide
    g := ![![![107, 3533, -8934], ![358, 16080, 0]], ![![11, 351, -889], ![40, 1600, 0]]]
    h := ![![![394, 53, -2], ![-3770, 27, 0]], ![![445, 62, -1], ![-4258, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {9} * I67N0 =  Ideal.span {B.equivFun.symm ![8, -3, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 177147 ![![67, 0, 0], ![11, 1, 0]]
  ![-107851, -6267, -5495] ![![177147, 0, 0], ![58506, 1, 0]] where
    su := ![![11868849, 0, 0], ![1948617, 177147, 0]]
    hsu := by decide
    w := ![![-19105481097, -1110180249, -973422765], ![-6310507581, -366694290, -321521805]]
    hw := by decide
    g := ![![![938562084717, -558331221820763163, -47714907774865], ![-2841818918083, 1690510553518802040, 0]], ![![1516861756096882605282, -902349745719260455332831100, -77114682494845664363425], ![-4592819702377439286191, 2732126931982884980997529700, 0]]]
    h := ![![![77059, -32954261, -13733965], ![-479164, 184034032, 0]], ![![25449, -10884736, -4536305], ![-158246, 60786124, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {177147} * I67N1 =  Ideal.span {B.equivFun.symm ![-107851, -6267, -5495]} * (J0 ^ 11) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 9 ![![67, 0, 0], ![-19, 1, 0]]
  ![34, 3, 2] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![603, 0, 0], ![-171, 9, 0]]
    hsu := by decide
    w := ![![306, 27, 18], ![108, 0, 9]]
    hw := by decide
    g := ![![![-5, -177, 447], ![-17, -804, 0]], ![![2, 51, -129], ![5, 232, 0]]]
    h := ![![![6034, -321, 1], ![21276, -13, 0]], ![![2152, -106, -2], ![7588, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {9} * I67N2 =  Ideal.span {B.equivFun.symm ![34, 3, 2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS2 
