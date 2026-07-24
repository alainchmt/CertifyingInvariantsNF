import IdealArithmetic.Examples.NF3_3_157300_2.PrimesBelow3_3_157300_2F1
import IdealArithmetic.Examples.NF3_3_157300_2.ClassGroupData3_3_157300_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 9 ![![37, 0, 0], ![-17, 1, 0]]
  ![-188, -235, -84] ![![9, 0, 0], ![1, 1, 0]] where
    su := ![![333, 0, 0], ![-153, 9, 0]]
    hsu := by decide
    w := ![![-1692, -2115, -756], ![-1935, -2439, -873]]
    hw := by decide
    g := ![![![-8993579, -8993608, -27646413], ![-1998573, 82939200, 74]], ![![4253712, 4253726, 13075979], ![945271, -39227920, -35]]]
    h := ![![![12338, -321357, 56775], ![-14327, -700253, 0]], ![![14096, -367182, 64871], ![-16373, -800108, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {9} * I37N1 =  Ideal.span {B.equivFun.symm ![-188, -235, -84]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 9 ![![41, 0, 0], ![-18, 1, 0]]
  ![-2, -7, -3] ![![9, 0, 0], ![1, 1, 0]] where
    su := ![![369, 0, 0], ![-162, 9, 0]]
    hsu := by decide
    w := ![![-18, -63, -27], ![-63, -81, -27]]
    hw := by decide
    g := ![![![-8492162, -8565169, -25475643], ![-1895259, 76353931, 109494]], ![![3602735, 3633708, 10807849], ![804050, -32392578, -46452]]]
    h := ![![![-14, 377, -63], ![16, 860, 0]], ![![-39, 1455, -243], ![96, 3320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {9} * I41N1 =  Ideal.span {B.equivFun.symm ![-2, -7, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS1 


noncomputable def E47RS1 : RelationCertificate Table 3 ![![47, 0, 0], ![10, 1, 0]]
  ![32, 43, -15] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![141, 0, 0], ![30, 3, 0]]
    hsu := by decide
    w := ![![96, 129, -45], ![-195, -285, 99]]
    hw := by decide
    g := ![![![-167551, -238464, -23630], ![-135335, 0, 35448]], ![![-35903, -51098, -5063], ![-29000, 0, 7596]]]
    h := ![![![-2745, -29933, -8988], ![-1176, 140807, 0]], ![![5535, 60573, 18189], ![2474, -284950, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {3} * I47N1 =  Ideal.span {B.equivFun.symm ![32, 43, -15]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 9 ![![53, 0, 0], ![4, 1, 0]]
  ![134, 199, -69] ![![9, 0, 0], ![1, 1, 0]] where
    su := ![![477, 0, 0], ![36, 9, 0]]
    hsu := by decide
    w := ![![1206, 1791, -621], ![-909, -1323, 459]]
    hw := by decide
    g := ![![![18772, 18777, 57899], ![4173, -173713, 21]], ![![2682, 2681, 8269], ![599, -24810, 3]]]
    h := ![![![-43514, -175930, -132045], ![-6599, 2332772, 0]], ![![32819, 132705, 99603], ![5032, -1759636, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {9} * I53N1 =  Ideal.span {B.equivFun.symm ![134, 199, -69]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 3 ![![53, 0, 0], ![-5, 1, 0]]
  ![67, 2, -3] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![159, 0, 0], ![-15, 3, 0]]
    hsu := by decide
    w := ![![201, 6, -9], ![15, -3, 0]]
    hw := by decide
    g := ![![![-157, -224, -23], ![-124, 0, 33]], ![![13, 19, 2], ![14, 0, -3]]]
    h := ![![![-4086, 20795, -12486], ![792, 220585, 0]], ![![-304, 1568, -942], ![105, 16642, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {3} * I53N2 =  Ideal.span {B.equivFun.symm ![67, 2, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS2 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![-11, 1, 0]]
  ![-137, -4, 6] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![177, 0, 0], ![-33, 3, 0]]
    hsu := by decide
    w := ![![-411, -12, 18], ![-33, 3, 0]]
    hw := by decide
    g := ![![![406, 579, 56], ![331, 0, -87]], ![![-71, -101, -10], ![-56, 0, 15]]]
    h := ![![![5301, -62380, 17022], ![-1988, -334764, 0]], ![![437, -5047, 1377], ![-117, -27081, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![-137, -4, 6]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E67RS1 : RelationCertificate Table 9 ![![67, 0, 0], ![31, 1, 0]]
  ![181, -10, -3] ![![9, 0, 0], ![1, 1, 0]] where
    su := ![![603, 0, 0], ![279, 9, 0]]
    hsu := by decide
    w := ![![1629, -90, -27], ![117, 99, -36]]
    hw := by decide
    g := ![![![-85652, -83325, -283390], ![-18772, 852517, -3484]], ![![-38989, -37929, -129005], ![-8539, 388087, -1586]]]
    h := ![![![13151, 630618, 61050], ![15565, -1363451, 0]], ![![851, 42165, 4082], ![1102, -91166, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {9} * I67N1 =  Ideal.span {B.equivFun.symm ![181, -10, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 9 ![![71, 0, 0], ![31, 1, 0]]
  ![-1, -8, 3] ![![9, 0, 0], ![1, 1, 0]] where
    su := ![![639, 0, 0], ![279, 9, 0]]
    hsu := by decide
    w := ![![-9, -72, 27], ![45, 63, -18]]
    hw := by decide
    g := ![![![-3365, -3286, -11210], ![-735, 33723, -142]], ![![-1446, -1412, -4816], ![-313, 14488, -61]]]
    h := ![![![-12, 61, 6], ![32, -141, 0]], ![![-13, -351, -34], ![4, 804, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {9} * I71N1 =  Ideal.span {B.equivFun.symm ![-1, -8, 3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 3 ![![73, 0, 0], ![14, 1, 0]]
  ![-86, -109, -39] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![219, 0, 0], ![42, 3, 0]]
    hsu := by decide
    w := ![![-258, -327, -117], ![-897, -1131, -405]]
    hw := by decide
    g := ![![![-850, -1431, -144], ![-760, 0, 210]], ![![-173, -286, -29], ![-150, 0, 42]]]
    h := ![![![1543, 23372, 5010], ![657, -121923, 0]], ![![5391, 81272, 17421], ![2151, -423956, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {3} * I73N1 =  Ideal.span {B.equivFun.symm ![-86, -109, -39]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 
