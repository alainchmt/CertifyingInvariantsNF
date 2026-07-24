import IdealArithmetic.Examples.NF3_1_551980_3.PrimesBelow3_1_551980_3F1
import IdealArithmetic.Examples.NF3_1_551980_3.ClassGroupData3_1_551980_3

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 9 ![![37, 0, 0], ![2, 1, 0]]
  ![-177850751642, 52425602018, -7203404989] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![333, 0, 0], ![18, 9, 0]]
    hsu := by decide
    w := ![![-1600656764778, 471830418162, -64830644901], ![1472229276579, -433973460447, 59629007007]]
    hw := by decide
    g := ![![![383153494814738, 16284023514973178, -8237800131141013], ![1724190725038198, 74140201180116890, 0]], ![![15533249862017, 660163115473921, -333964870183768], ![69899623972216, 3005683831629759, 0]]]
    h := ![![![-2862951236474, -1432067124574, -2400588139], ![52875672498948, 81618356154, 0]], ![![2633244503441, 1317166298990, 2207978759], ![-48633232798293, -75069768860, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {9} * I37N1 =  Ideal.span {B.equivFun.symm ![-177850751642, 52425602018, -7203404989]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 9 ![![41, 0, 0], ![11, 1, 0]]
  ![-254084, 368852, 65201] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![369, 0, 0], ![99, 9, 0]]
    hsu := by decide
    w := ![![-2286756, 3319668, 586809], ![-9597987, 377433, 303651]]
    hw := by decide
    g := ![![![25216950688, -7141516898, 1078926339], ![-6397268696, 26240, 0]], ![![2904321239, -822511711, 124263146], ![-736794904, 6960, 0]]]
    h := ![![![-822754, -72092, 967], ![3043530, 25554, 0]], ![![-3526738, -343492, -1565], ![13048165, 97904, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {9} * I41N1 =  Ideal.span {B.equivFun.symm ![-254084, 368852, 65201]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E41RS1 


noncomputable def E53RS0 : RelationCertificate Table 9 ![![53, 0, 0], ![4, 1, 0]]
  ![308, -20, -11] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![477, 0, 0], ![36, 9, 0]]
    hsu := by decide
    w := ![![2772, -180, -99], ![1089, 117, -9]]
    hw := by decide
    g := ![![![-2880, -140548, 71058], ![-14972, -639359, 0]], ![![-439, -17902, 9058], ![-1889, -81529, 0]]]
    h := ![![![9564, 2402, 3], ![-126646, -170, 0]], ![![3757, 943, 1], ![-49750, -54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {9} * I53N0 =  Ideal.span {B.equivFun.symm ![308, -20, -11]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS0 


noncomputable def E53RS2 : RelationCertificate Table 3 ![![53, 0, 0], ![-19, 1, 0]]
  ![2168795852, -639302489, 87841714] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![159, 0, 0], ![-57, 3, 0]]
    hsu := by decide
    w := ![![6506387556, -1917907467, 263525142], ![-11446669818, 3374169357, -463619061]]
    hw := by decide
    g := ![![![-90296, 2650, 17683], ![-29215, -58072, 0]], ![![37043, -3608, -6753], ![11145, 20468, 0]]]
    h := ![![![16041980962, -918060361, 5017232], ![44634536586, -178071582, 0]], ![![-28222613154, 1615141106, -8826804], ![-78525417924, 313280925, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {3} * I53N2 =  Ideal.span {B.equivFun.symm ![2168795852, -639302489, 87841714]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS2 


noncomputable def E59RS1 : RelationCertificate Table 9 ![![59, 0, 0], ![-19, 1, 0]]
  ![-2276509006, 671053420, -92204369] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![531, 0, 0], ![-171, 9, 0]]
    hsu := by decide
    w := ![![-20488581054, 6039480780, -829839321], ![18844695207, -5554907595, 763257789]]
    hw := by decide
    g := ![![![-58924, 11631, -1641], ![14395, 36344, 0]], ![![12967, -4107, 665], ![-3334, -11781, 0]]]
    h := ![![![-26910440786, 1526093269, -6847590], ![-83444184072, 311803441, 0]], ![![24751301909, -1403648314, 6298178], ![76749103032, -286786081, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {9} * I59N1 =  Ideal.span {B.equivFun.symm ![-2276509006, 671053420, -92204369]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 


noncomputable def E73RS0 : RelationCertificate Table 9 ![![73, 0, 0], ![-33, 1, 0]]
  ![99788, 1795, -2246] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![657, 0, 0], ![-297, 9, 0]]
    hsu := by decide
    w := ![![898092, 16155, -20214], ![148554, 49032, 4041]]
    hw := by decide
    g := ![![![34091977, -129836, -3337566], ![-7590413, 43080257, 0]], ![![-18325678, 818774, 1416925], ![4163351, -19769704, 0]]]
    h := ![![![2002958, -67816, 187], ![4427762, -15897, 0]], ![![330576, -11119, 42], ![730774, -2617, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {9} * I73N0 =  Ideal.span {B.equivFun.symm ![99788, 1795, -2246]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS0 


noncomputable def E73RS1 : RelationCertificate Table 3 ![![73, 0, 0], ![-27, 1, 0]]
  ![-612086737, 180426652, -24791060] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![219, 0, 0], ![-81, 3, 0]]
    hsu := by decide
    w := ![![-1836260211, 541279956, -74373180], ![3230527563, -952272345, 130844532]]
    hw := by decide
    g := ![![![27856, -18003, -3244], ![3285, -656, 0]], ![![-3612, 5916, 1436], ![769, -1312, 0]]]
    h := ![![![-54046598125, 2197282817, -7502415], ![-146103317644, 522885235, 0]], ![![95084032257, -3865673591, 13198976], ![257039167120, -919910404, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {3} * I73N1 =  Ideal.span {B.equivFun.symm ![-612086737, 180426652, -24791060]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 
