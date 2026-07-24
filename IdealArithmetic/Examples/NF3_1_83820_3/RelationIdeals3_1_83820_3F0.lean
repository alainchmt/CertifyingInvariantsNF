import IdealArithmetic.Examples.NF3_1_83820_3.PrimesBelow3_1_83820_3F0
import IdealArithmetic.Examples.NF3_1_83820_3.ClassGroupData3_1_83820_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 9 ![![2, 0, 0], ![-15, 1, 1]]
  ![1871, -687, 157] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![18, 0, 0], ![-135, 9, 9]]
    hsu := by decide
    w := ![![16839, -6183, 1413], ![-21987, 8073, -1845]]
    hw := by decide
    g := ![![![-15, -4, 2], ![11, -6, 0]], ![![98, 10, -18], ![-35, 46, 0]]]
    h := ![![![48647, 274258, -2131], ![-228685, 0, 29138]], ![![-63497, -358105, 2781], ![298601, 0, -38046]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {9} * I2N0 =  Ideal.span {B.equivFun.symm ![1871, -687, 157]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 3 ![![3, 0, 0], ![0, 1, 0]]
  ![-1166, 63, 56] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![9, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![-3498, 189, 168], ![-3699, 3, 126]]
    hw := by decide
    g := ![![![9009, -2498, 860], ![-3834, 5, 0]], ![![-23280, 6457, -2232], ![9913, 2, 0]]]
    h := ![![![-364, 36, 68], ![-45, -74, 0]], ![![-384, 0, 68], ![1, -81, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {3} * I3N0 =  Ideal.span {B.equivFun.symm ![-1166, 63, 56]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![3, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![1, 1, 0]]
  ![187925, -69000, 15769] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![15, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![563775, -207000, 47307], ![-1644597, 603843, -138000]]
    hw := by decide
    g := ![![![871, 90, -19], ![-257, -16, 0]], ![![655, 121, -8], ![-178, 0, 0]]]
    h := ![![![-2518, -53903, -31881], ![112928, 87587, 0]], ![![7340, 157236, 92998], ![-329404, -255495, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![187925, -69000, 15769]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 3 ![![5, 0, 0], ![2, 1, 0]]
  ![-4465, 594, 307] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![15, 0, 0], ![6, 3, 0]]
    hsu := by decide
    w := ![![-13395, 1782, 921], ![-21957, 1695, 1188]]
    hw := by decide
    g := ![![![214746, -59465, 20267], ![-91402, 484, 0]], ![![-247251, 68636, -23889], ![105296, 308, 0]]]
    h := ![![![1268, 5396, 5657], ![1592, -13989, 0]], ![![2027, 8615, 9088], ![2534, -22522, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {3} * I5N1 =  Ideal.span {B.equivFun.symm ![-4465, 594, 307]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![1, 1, 0]]
  ![17, 6, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![33, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![51, 18, 3], ![-99, 33, 12]]
    hw := by decide
    g := ![![![24, 9, -49], ![-4, 80, 0]], ![![-29, 9, -8], ![16, 8, 0]]]
    h := ![![![-2, -3, -3], ![22, 17, 0]], ![![-13, -9, -20], ![-2, 112, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![17, 6, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![-1, 1, 0]]
  ![-2729, 1002, -229] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![33, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![-8187, 3006, -687], ![23883, -8769, 2004]]
    hw := by decide
    g := ![![![-198, -11, 11], ![65, -1, 0]], ![![-56, -6, 2], ![17, 0, 0]]]
    h := ![![![329, -486, 1145], ![-64, -6412, 0]], ![![-957, 1415, -3340], ![216, 18704, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![-2729, 1002, -229]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 3 ![![13, 0, 0], ![6, 1, 0]]
  ![-4600, 1689, -386] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![39, 0, 0], ![18, 3, 0]]
    hsu := by decide
    w := ![![-13800, 5067, -1158], ![40257, -14781, 3378]]
    hw := by decide
    g := ![![![-554, 659, -1544], ![406, 2320, 0]], ![![-325, 368, -846], ![234, 1276, 0]]]
    h := ![![![88660, 812708, 273482], ![103441, -1777826, 0]], ![![-258643, -2370810, -797794], ![-301741, 5186224, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {3} * I13N0 =  Ideal.span {B.equivFun.symm ![-4600, 1689, -386]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 9 ![![13, 0, 0], ![-5, 1, 0]]
  ![-11929, 4380, -1001] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![117, 0, 0], ![-45, 9, 0]]
    hsu := by decide
    w := ![![-107361, 39420, -9009], ![140184, -51471, 11763]]
    hw := by decide
    g := ![![![-7290, 42152, -21501], ![7925, 96784, 0]], ![![2347, -13742, 7014], ![-2563, -31560, 0]]]
    h := ![![![13862, -97179, 39323], ![-12793, -256100, 0]], ![![-18090, 126887, -51345], ![16730, 334396, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {9} * I13N1 =  Ideal.span {B.equivFun.symm ![-11929, 4380, -1001]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![2, 1, 0]]
  ![203, 30, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![51, 0, 0], ![6, 3, 0]]
    hsu := by decide
    w := ![![609, 90, 3], ![-261, 195, 60]]
    hw := by decide
    g := ![![![1860, -515, 175], ![-791, 5, 0]], ![![-629, 174, -61], ![271, 1, 0]]]
    h := ![![![-504, -1049, -1057], ![-107, 8985, 0]], ![![237, 499, 500], ![62, -4240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![203, 30, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 3 ![![19, 0, 0], ![9, 1, 0]]
  ![-2869, 3018, 889] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![57, 0, 0], ![27, 3, 0]]
    hsu := by decide
    w := ![![-8607, 9054, 2667], ![-72345, 13671, 6036]]
    hw := by decide
    g := ![![![-7030658, 1949961, -673681], ![2993542, 0, 0]], ![![-462042, 128146, -44268], ![196731, -8, 0]]]
    h := ![![![86319, 1221252, 272631], ![105180, -2589550, 0]], ![![690876, 9773332, 2181748], ![841649, -20725600, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {3} * I19N1 =  Ideal.span {B.equivFun.symm ![-2869, 3018, 889]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 3 ![![23, 0, 0], ![3, 1, 0]]
  ![-3667, 1806, 598] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![69, 0, 0], ![9, 3, 0]]
    hsu := by decide
    w := ![![-11001, 5418, 1794], ![-47151, 7683, 3612]]
    hw := by decide
    g := ![![![2236630, -620329, 214304], ![-952318, 17, 0]], ![![-462045, 128149, -44276], ![196734, 4, 0]]]
    h := ![![![78367, 242894, 162506], ![20804, -1868520, 0]], ![![322836, 1000452, 669428], ![85625, -7697820, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {3} * I23N1 =  Ideal.span {B.equivFun.symm ![-3667, 1806, 598]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 9 ![![29, 0, 0], ![-6, 1, 0]]
  ![-2131, 312, 154] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![261, 0, 0], ![-54, 9, 0]]
    hsu := by decide
    w := ![![-19179, 2808, 1386], ![-4716, 9, 162]]
    hw := by decide
    g := ![![![5921, -2191, 534], ![-2869, 328, 0]], ![![-2812, 1079, -274], ![1374, -62, 0]]]
    h := ![![![-423563, 2761682, -922654], ![182894, 13378560, 0]], ![![-103526, 675014, -225518], ![44715, 3270020, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {9} * I29N1 =  Ideal.span {B.equivFun.symm ![-2131, 312, 154]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E29RS1 
