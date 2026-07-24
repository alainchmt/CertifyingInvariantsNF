import IdealArithmetic.Examples.NF3_1_677484_9.PrimesBelow3_1_677484_9F2
import IdealArithmetic.Examples.NF3_1_677484_9.ClassGroupData3_1_677484_9

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 121 ![![83, 0, 0], ![8, 1, 0]]
  ![262907, 4040, -6566] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![10043, 0, 0], ![968, 121, 0]]
    hsu := by decide
    w := ![![31811747, 488840, -794486], ![-9318331, -90629, 214654]]
    hw := by decide
    g := ![![![-3522065, -2019007191, 417782488], ![-15841794, -8424905337, 0]], ![![-285220, -194812674, 40317838], ![-1541608, -812961441, 0]]]
    h := ![![![223365961, 28210802, 217724], ![-2317388982, -3012943, 0]], ![![-65427649, -8263423, -63784], ![678802232, 882641, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {121} * I83N1 =  Ideal.span {B.equivFun.symm ![262907, 4040, -6566]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS1 


noncomputable def E97RS0 : RelationCertificate Table 121 ![![97, 0, 0], ![10, 1, 0]]
  ![141487, -5886, -763] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![11737, 0, 0], ![1210, 121, 0]]
    hsu := by decide
    w := ![![17119927, -712206, -92323], ![-4299977, 284713, -13189]]
    hw := by decide
    g := ![![![281703, 93723, 12985], ![-66662, 144288, 0]], ![![79745, 20898, 4840], ![-18823, 17352, 0]]]
    h := ![![![146340491, 14812754, 107339], ![-1419488614, -1735441, 0]], ![![-36753841, -3720263, -26965], ![356508704, 435916, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {121} * I97N0 =  Ideal.span {B.equivFun.symm ![141487, -5886, -763]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 11 ![![97, 0, 0], ![18, 1, 0]]
  ![-97, -18, -6] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![1067, 0, 0], ![198, 11, 0]]
    hsu := by decide
    w := ![![-1067, -198, -66], ![-1936, -385, -132]]
    hw := by decide
    g := ![![![7, -304, -462], ![-22, 846, 0]], ![![-2, -60, -90], ![1, 165, 0]]]
    h := ![![![-451, -43, -6], ![2425, 96, 0]], ![![-812, -63, -6], ![4366, 95, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {11} * I97N1 =  Ideal.span {B.equivFun.symm ![-97, -18, -6]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS1 


noncomputable def E103RS0 : RelationCertificate Table 121 ![![103, 0, 0], ![3, 1, 0]]
  ![-1121, -119, 63] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![12463, 0, 0], ![363, 121, 0]]
    hsu := by decide
    w := ![![-135641, -14399, 7623], ![48763, 4598, -2541]]
    hw := by decide
    g := ![![![3602081, 1922995703, -397886877], ![15029318, 8024052037, 0]], ![![130672, 69749703, -14431905], ![545207, 291043421, 0]]]
    h := ![![![-390032, -130124, -231], ![13390725, 3976, 0]], ![![140212, 46777, 81], ![-4813811, -1394, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {121} * I103N0 =  Ideal.span {B.equivFun.symm ![-1121, -119, 63]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS0 


noncomputable def E103RS2 : RelationCertificate Table 11 ![![103, 0, 0], ![-32, 1, 0]]
  ![-16111, -3171, -1090] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![1133, 0, 0], ![-352, 11, 0]]
    hsu := by decide
    w := ![![-177221, -34881, -11990], ![-345664, -68035, -23386]]
    hw := by decide
    g := ![![![-369, -550, -836], ![-179, 1550, 0]], ![![132, 166, 256], ![73, -475, 0]]]
    h := ![![![-204185, 6758, -88], ![-656717, 1329, 0]], ![![-398272, 13173, -170], ![-1280956, 2564, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {11} * I103N2 =  Ideal.span {B.equivFun.symm ![-16111, -3171, -1090]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS2 


noncomputable def E127RS0 : RelationCertificate Table 11 ![![127, 0, 0], ![59, 1, 0]]
  ![-55501, -10924, -3755] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![1397, 0, 0], ![649, 11, 0]]
    hsu := by decide
    w := ![![-610511, -120164, -41305], ![-1190794, -234377, -80564]]
    hw := by decide
    g := ![![![-597, -1184, -1681], ![-317, 3150, 0]], ![![-211, -548, -785], ![-122, 1465, 0]]]
    h := ![![![-601503, -12451, -251], ![1293820, 4687, 0]], ![![-1173240, -24290, -490], ![2523614, 9151, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {11} * I127N0 =  Ideal.span {B.equivFun.symm ![-55501, -10924, -3755]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E127RS0 


noncomputable def E127RS2 : RelationCertificate Table 121 ![![127, 0, 0], ![-13, 1, 0]]
  ![-11057, 744, -38] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![15367, 0, 0], ![-1573, 121, 0]]
    hsu := by decide
    w := ![![-1337897, 90024, -4598], ![310849, -34001, 5566]]
    hw := by decide
    g := ![![![-1602361, -856903126, 177302066], ![-6697714, -3575587740, 0]], ![![76908, 40995932, -8482454], ![320471, 171062960, 0]]]
    h := ![![![-18429751, 1431482, -6374], ![-180043640, 134910, 0]], ![![4282271, -332612, 1480], ![41834296, -31319, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {121} * I127N2 =  Ideal.span {B.equivFun.symm ![-11057, 744, -38]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E127RS2 


noncomputable def E137RS0 : RelationCertificate Table 11 ![![137, 0, 0], ![55, 1, 0]]
  ![4621, -64, -69] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![1507, 0, 0], ![605, 11, 0]]
    hsu := by decide
    w := ![![50831, -704, -759], ![682, 1881, -660]]
    hw := by decide
    g := ![![![98919, -4023747, -6075813], ![-329816, 11136384, 0]], ![![38971, -1670971, -2522709], ![-137733, 4623588, 0]]]
    h := ![![![9018, 140, -3], ![-22379, 57, 0]], ![![96, -48, -6], ![-238, 127, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {11} * I137N0 =  Ideal.span {B.equivFun.symm ![4621, -64, -69]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 11 ![![137, 0, 0], ![-29, 1, 0]]
  ![-3593, -707, -243] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![1507, 0, 0], ![-319, 11, 0]]
    hsu := by decide
    w := ![![-39523, -7777, -2673], ![-77066, -15169, -5214]]
    hw := by decide
    g := ![![![133393, -4570906, -6906423], ![-367018, 12661772, 0]], ![![-26719, 915376, 1383093], ![73507, -2535669, 0]]]
    h := ![![![-49449, 1763, -15], ![-233480, 302, 0]], ![![-96470, 3443, -30], ![-455496, 606, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {11} * I137N1 =  Ideal.span {B.equivFun.symm ![-3593, -707, -243]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 11 ![![137, 0, 0], ![-26, 1, 0]]
  ![220247, 43350, 14901] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![1507, 0, 0], ![-286, 11, 0]]
    hsu := by decide
    w := ![![2422717, 476850, 163911], ![4725446, 930083, 319704]]
    hw := by decide
    g := ![![![-88995, 3009999, 4547865], ![241286, -8337728, 0]], ![![15956, -538576, -813732], ![-43155, 1491840, 0]]]
    h := ![![![2936715, -115806, 855], ![15465758, -17039, 0]], ![![5727958, -225877, 1668], ![30165410, -33242, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {11} * I137N2 =  Ideal.span {B.equivFun.symm ![220247, 43350, 14901]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E137RS2 
