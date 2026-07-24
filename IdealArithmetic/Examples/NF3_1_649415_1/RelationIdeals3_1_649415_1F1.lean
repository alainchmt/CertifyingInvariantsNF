import IdealArithmetic.Examples.NF3_1_649415_1.PrimesBelow3_1_649415_1F1
import IdealArithmetic.Examples.NF3_1_649415_1.ClassGroupData3_1_649415_1

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 3 ![![41, 0, 0], ![10, 1, 0]]
  ![47, -9, 2] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![123, 0, 0], ![30, 3, 0]]
    hsu := by decide
    w := ![![141, -27, 6], ![249, 81, -45]]
    hw := by decide
    g := ![![![-371, -85, -27], ![97, 0, 0]], ![![-192, -39, -27], ![53, 8, 0]]]
    h := ![![![8693, 42514, 23662], ![3169, -194028, 0]], ![![15141, 74036, 41205], ![5507, -337884, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {3} * I41N0 =  Ideal.span {B.equivFun.symm ![47, -9, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS0 


noncomputable def E41RS2 : RelationCertificate Table 2187 ![![41, 0, 0], ![-2, 1, 0]]
  ![10037, -861, -31] ![![2187, 0, 0], ![-1057, 1, 0]] where
    su := ![![89667, 0, 0], ![-4374, 2187, 0]]
    hsu := by decide
    w := ![![21950919, -1883007, -67797], ![-10615698, 920727, 28431]]
    hw := by decide
    g := ![![![36497, -26554336, 125494], ![-28373, -54890704, 0]], ![![-1025, 1195366, -5649], ![2549, 2470952, 0]]]
    h := ![![![196113, -294639, 491709], ![-16722, -4032020, 0]], ![![-94846, 142497, -237807], ![8104, 1950020, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {2187} * I41N2 =  Ideal.span {B.equivFun.symm ![10037, -861, -31]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E41RS2 


noncomputable def E47RS1 : RelationCertificate Table 27 ![![47, 0, 0], ![2, 1, 0]]
  ![-5312, -2703, 1381] ![![27, 0, 0], ![-4, 1, 0]] where
    su := ![![1269, 0, 0], ![54, 27, 0]]
    hsu := by decide
    w := ![![-143424, -72981, 37287], ![232659, 19251, -17658]]
    hw := by decide
    g := ![![![-464653, 44178, -132407], ![70490, 558376, 0]], ![![-117023, -11548, -12323], ![16931, 24024, 0]]]
    h := ![![![-1228, -615, -2762], ![-37, 26239, 0]], ![![709, 278, 1308], ![73, -12426, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {27} * I47N1 =  Ideal.span {B.equivFun.symm ![-5312, -2703, 1381]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E47RS1 


noncomputable def E59RS0 : RelationCertificate Table 729 ![![59, 0, 0], ![18, 1, 0]]
  ![-5231, -678, -347] ![![729, 0, 0], ![-328, 1, 0]] where
    su := ![![43011, 0, 0], ![13122, 729, 0]]
    hsu := by decide
    w := ![![-3813399, -494262, -252963], ![1659933, 215055, 110079]]
    hw := by decide
    g := ![![![1020507904, -224666333303, 3414397962], ![-767342021, -497819222857, 0]], ![![325235965, -71601161839, 1088168652], ![-244551708, -158654989460, 0]]]
    h := ![![![152559885, 1481353171, 436049292], ![71651388, -5145381715, 0]], ![![-66407915, -644819224, -189808191], ![-31189117, 2239736684, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {729} * I59N0 =  Ideal.span {B.equivFun.symm ![-5231, -678, -347]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![-15, 1, 0]]
  ![-95842, -12510, -6409] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![177, 0, 0], ![-45, 3, 0]]
    hsu := by decide
    w := ![![-287526, -37530, -19227], ![-935391, -122094, -62550]]
    hw := by decide
    g := ![![![947, 19, -6], ![-308, 0, 0]], ![![-260, 14, -19], ![93, 8, 0]]]
    h := ![![![-3558348, 31349984, -9804651], ![1436034, 115693600, 0]], ![![-11576160, 101989013, -31896880], ![4671759, 376379014, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![-95842, -12510, -6409]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 3 ![![59, 0, 0], ![-3, 1, 0]]
  ![-7, 3, -1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![177, 0, 0], ![-9, 3, 0]]
    hsu := by decide
    w := ![![-21, 9, -3], ![-144, -21, 15]]
    hw := by decide
    g := ![![![25475, -25432, 77736], ![-16969, -46640, 0]], ![![-1151, 1157, -3533], ![771, 2120, 0]]]
    h := ![![![-1481, 2973, -3719], ![132, 43884, 0]], ![![-10008, 20089, -25130], ![882, 296535, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {3} * I59N2 =  Ideal.span {B.equivFun.symm ![-7, 3, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS2 


noncomputable def E71RS1 : RelationCertificate Table 2187 ![![71, 0, 0], ![-10, 1, 0]]
  ![3247340, 423867, 217151] ![![2187, 0, 0], ![-1057, 1, 0]] where
    su := ![![155277, 0, 0], ![-21870, 2187, 0]]
    hsu := by decide
    w := ![![7101932580, 926997129, 474909237], ![-3397497939, -443466738, -227192121]]
    hw := by decide
    g := ![![![-25918, 19848407, -93801], ![24023, 41028820, 0]], ![![3663, -2594029, 12259], ![-2572, -5362140, 0]]]
    h := ![![![-94621422660, 536299001521, -243905945419], ![20880468056, 3463464468380, 0]], ![![45266001163, -256560412451, 116682316727], ![-9989020053, -1656888918300, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {2187} * I71N1 =  Ideal.span {B.equivFun.symm ![3247340, 423867, 217151]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 3 ![![73, 0, 0], ![-27, 1, 0]]
  ![6154, 141, -308] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![219, 0, 0], ![-81, 3, 0]]
    hsu := by decide
    w := ![![18462, 423, -924], ![-54228, 3408, 705]]
    hw := by decide
    g := ![![![1758412, 400080, 127821], ![-452777, -88, 0]], ![![-391200, -88999, -28457], ![100734, 32, 0]]]
    h := ![![![29827, -509174, 90964], ![-17965, -1328136, 0]], ![![-87822, 1500358, -268045], ![53114, 3913504, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {3} * I73N1 =  Ideal.span {B.equivFun.symm ![6154, 141, -308]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 
