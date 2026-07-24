import IdealArithmetic.Examples.NF3_1_119660_3.PrimesBelow3_1_119660_3F0
import IdealArithmetic.Examples.NF3_1_119660_3.ClassGroupData3_1_119660_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 3 ![![2, 0, 0], ![0, 1, 0]]
  ![-80, 27, -1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![6, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![-240, 81, -3], ![-66, -72, 27]]
    hw := by decide
    g := ![![![1422, 222, 73], ![76, 0, 0]], ![![2409, 377, 121], ![126, 8, 0]]]
    h := ![![![-40, 10, 0], ![7, -1, 0]], ![![-11, -10, 0], ![-4, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {3} * I2N0 =  Ideal.span {B.equivFun.symm ![-80, 27, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 9 ![![3, 0, 0], ![1, 1, 0]]
  ![-1, -3, 1] ![![9, 0, 0], ![3, 1, 0]] where
    su := ![![27, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![-9, -27, 9], ![63, -18, 0]]
    hw := by decide
    g := ![![![-35, 1103, 372], ![118, -3346, 0]], ![![-27, 946, 319], ![100, -2868, 0]]]
    h := ![![![0, 0, 1], ![-1, -2, 0]], ![![2, -1, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {9} * I3N1 =  Ideal.span {B.equivFun.symm ![-1, -3, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 9 ![![5, 0, 0], ![1, 1, 0]]
  ![137, 24, 7] ![![9, 0, 0], ![3, 1, 0]] where
    su := ![![45, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![1233, 216, 63], ![873, 153, 45]]
    hw := by decide
    g := ![![![-2, 13, 5], ![9, -44, 0]], ![![1, 3, 1], ![2, -10, 0]]]
    h := ![![![25, 25, 24], ![12, -113, 0]], ![![34, 18, 1], ![-73, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {9} * I5N0 =  Ideal.span {B.equivFun.symm ![137, 24, 7]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 9 ![![5, 0, 0], ![2, 1, 0]]
  ![2661739, -440178, -101950] ![![9, 0, 0], ![3, 1, 0]] where
    su := ![![45, 0, 0], ![18, 9, 0]]
    hsu := by decide
    w := ![![23955651, -3961602, -917550], ![1256517, 2156805, -746028]]
    hw := by decide
    g := ![![![-118056772846, -18334876581, -6768783670], ![-41389466121, 10504, 0]], ![![-127221702299, -19758239868, -7294254294], ![-44602594081, 6868, 0]]]
    h := ![![![26861797, 16141913, 1512222], ![-65823623, -7663060, 0]], ![![2004475, 1191008, 60823], ![-4941381, -387007, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {9} * I5N1 =  Ideal.span {B.equivFun.symm ![2661739, -440178, -101950]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS1 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![0, 1, 0]]
  ![-9691, 702, 637] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![33, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![-29073, 2106, 1911], ![42042, -14787, 702]]
    hw := by decide
    g := ![![![-21453813, -3358384, -1101347], ![-1119460, 0, 0]], ![![-6608082, -1034431, -339228], ![-344808, -8, 0]]]
    h := ![![![-881, 63, 0], ![9, 637, 0]], ![![1274, -445, 0], ![-34, 234, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![-9691, 702, 637]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS2 : RelationCertificate Table 9 ![![11, 0, 0], ![-5, 1, 0]]
  ![-47725, -8301, -2450] ![![9, 0, 0], ![3, 1, 0]] where
    su := ![![99, 0, 0], ![-45, 9, 0]]
    hsu := by decide
    w := ![![-429525, -74709, -22050], ![-304875, -53028, -15651]]
    hw := by decide
    g := ![![![35, -10, -8], ![16, 33, 0]], ![![-41, 12, 4], ![-10, -16, 0]]]
    h := ![![![-2368540, 543782, -14562], ![-5201243, 157732, 0]], ![![-1681180, 385974, -10336], ![-3691821, 111957, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {9} * I11N2 =  Ideal.span {B.equivFun.symm ![-47725, -8301, -2450]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS2 


noncomputable def E13RS1 : RelationCertificate Table 3 ![![13, 0, 0], ![3, 1, 0]]
  ![-355475, 181164, -22504] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![39, 0, 0], ![9, 3, 0]]
    hsu := by decide
    w := ![![-1066425, 543492, -67512], ![-1485264, -175443, 181164]]
    hw := by decide
    g := ![![![62491085857, 9782365395, 3208025077], ![3260788467, -23, 0]], ![![30707916319, 4807022535, 1576413086], ![1602340846, -6, 0]]]
    h := ![![![-1981004, -686076, -17995], ![8465859, 211431, 0]], ![![-2842390, -1006138, -17645], ![12151994, 289773, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {3} * I13N1 =  Ideal.span {B.equivFun.symm ![-355475, 181164, -22504]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![-8, 1, 0]]
  ![-943, -30, 91] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![51, 0, 0], ![-24, 3, 0]]
    hsu := by decide
    w := ![![-2829, -90, 273], ![6006, -1671, -30]]
    hw := by decide
    g := ![![![331069, 51825, 19377], ![17277, -7144, 0]], ![![-89814, -14060, -5624], ![-4685, 3040, 0]]]
    h := ![![![-23703, 3453, -57], ![-50251, 1060, 0]], ![![50994, -7429, 129], ![108112, -2203, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![-943, -30, 91]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E31RS0 : RelationCertificate Table 9 ![![31, 0, 0], ![7, 1, 0]]
  ![-73039, -12792, 10138] ![![9, 0, 0], ![3, 1, 0]] where
    su := ![![279, 0, 0], ![63, 9, 0]]
    hsu := by decide
    w := ![![-657351, -115128, 91242], ![449991, -192519, 17622]]
    hw := by decide
    g := ![![![-371731426, -57515959, -21240378], ![-130301133, -651820, 0]], ![![-124567118, -19296951, -7125525], ![-43666477, -147913, 0]]]
    h := ![![![-132424, -20009, 182], ![576015, 4496, 0]], ![![89800, 12642, 168], ![-390543, -3250, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {9} * I31N0 =  Ideal.span {B.equivFun.symm ![-73039, -12792, 10138]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 9 ![![31, 0, 0], ![-14, 1, 0]]
  ![1291, -276, -31] ![![9, 0, 0], ![3, 1, 0]] where
    su := ![![279, 0, 0], ![-126, 9, 0]]
    hsu := by decide
    w := ![![11619, -2484, -279], ![1827, 711, -369]]
    hw := by decide
    g := ![![![33589, -203305, -68388], ![-11388, 629257, 0]], ![![-12136, 88668, 29839], ![5812, -273263, 0]]]
    h := ![![![198661, -16072, 133], ![439800, -4154, 0]], ![![30905, -2489, 19], ![68418, -630, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {9} * I31N1 =  Ideal.span {B.equivFun.symm ![1291, -276, -31]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 
