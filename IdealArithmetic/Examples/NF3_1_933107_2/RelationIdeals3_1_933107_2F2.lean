import IdealArithmetic.Examples.NF3_1_933107_2.PrimesBelow3_1_933107_2F2
import IdealArithmetic.Examples.NF3_1_933107_2.ClassGroupData3_1_933107_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 50 ![![83, 0, 0], ![39, 1, 0]]
  ![-548333, 165061, -19157] ![![50, 0, 0], ![22, 1, 0]] where
    su := ![![4150, 0, 0], ![1950, 50, 0]]
    hsu := by decide
    w := ![![-27416650, 8253050, -957850], ![-7887100, 2374200, -275550]]
    hw := by decide
    g := ![![![-36920101, 5007675052, 227697878], ![83908660, -11384893717, 0]], ![![-17199751, 2332892797, 106076120], ![39090011, -5303805918, 0]]]
    h := ![![![-410141650, -15452248, -126845], ![872851503, 10508978, 0]], ![![-117987766, -4445266, -36491], ![251098124, 3023242, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {50} * I83N1 =  Ideal.span {B.equivFun.symm ![-548333, 165061, -19157]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 100 ![![89, 0, 0], ![40, 1, 0]]
  ![-117, 39, 7] ![![100, 0, 0], ![22, 1, 0]] where
    su := ![![8900, 0, 0], ![4000, 100, 0]]
    hsu := by decide
    w := ![![-11700, 3900, 700], ![-4100, 1000, 200]]
    hw := by decide
    g := ![![![12, -15617, -710], ![-63, 70992, 0]], ![![2, -7611, -346], ![-12, 34597, 0]]]
    h := ![![![-194973, -6837, -49], ![433812, 4368, 0]], ![![-68449, -2432, -18], ![152298, 1604, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {100} * I89N1 =  Ideal.span {B.equivFun.symm ![-117, 39, 7]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E89RS1 


noncomputable def E97RS0 : RelationCertificate Table 20 ![![97, 0, 0], ![26, 1, 0]]
  ![-93, 11, 3] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![1940, 0, 0], ![520, 20, 0]]
    hsu := by decide
    w := ![![-1860, 220, 60], ![-840, 40, 20]]
    hw := by decide
    g := ![![![61701193, -12463642500, -6247246551], ![-617011992, 124944931015, 0]], ![![15902412, -3212287693, -1610119450], ![-159024131, 32202388999, 0]]]
    h := ![![![-33679, -1426, -5], ![125645, 488, 0]], ![![-15230, -664, -3], ![56818, 292, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {20} * I97N0 =  Ideal.span {B.equivFun.symm ![-93, 11, 3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 20 ![![97, 0, 0], ![-15, 1, 0]]
  ![-59221, 17827, -2069] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![1940, 0, 0], ![-300, 20, 0]]
    hsu := by decide
    w := ![![-1184420, 356540, -41380], ![332600, -100120, 11620]]
    hw := by decide
    g := ![![![18533368259, -3743740335451, -1876503509731], ![-185333679932, 37530070194547, 0]], ![![-3057050385, 617524170825, 309526348001], ![30570503521, -6190526960008, 0]]]
    h := ![![![-150868, 10391, -34], ![-971665, 1229, 0]], ![![42370, -2910, 9], ![272884, -292, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {20} * I97N1 =  Ideal.span {B.equivFun.symm ![-59221, 17827, -2069]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E97RS1 


noncomputable def E97RS2 : RelationCertificate Table 20 ![![97, 0, 0], ![-12, 1, 0]]
  ![-11, -3, 1] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![1940, 0, 0], ![-240, 20, 0]]
    hsu := by decide
    w := ![![-220, -60, 20], ![-240, 20, 0]]
    hw := by decide
    g := ![![![3, -837, -419], ![-29, 8379, 0]], ![![-2, 97, 49], ![21, -980, 0]]]
    h := ![![![-2675, 235, -1], ![-21622, 98, 0]], ![![-2916, 255, -1], ![-23570, 97, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N2 : Ideal.span {20} * I97N2 =  Ideal.span {B.equivFun.symm ![-11, -3, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E97RS2 


noncomputable def E101RS1 : RelationCertificate Table 10 ![![101, 0, 0], ![22, 1, 0]]
  ![-1241, -3, 21] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![1010, 0, 0], ![220, 10, 0]]
    hsu := by decide
    w := ![![-12410, -30, 210], ![-7060, -470, 60]]
    hw := by decide
    g := ![![![8049, -557278, -281859], ![-54113, 2817621, 0]], ![![2232, -135914, -68687], ![-13135, 686732, 0]]]
    h := ![![![-5675, -284, -1], ![25997, 122, 0]], ![![-3246, -171, -1], ![14870, 107, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {10} * I101N1 =  Ideal.span {B.equivFun.symm ![-1241, -3, 21]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 100 ![![103, 0, 0], ![-45, 1, 0]]
  ![-1041, -53, 11] ![![100, 0, 0], ![22, 1, 0]] where
    su := ![![10300, 0, 0], ![-4500, 100, 0]]
    hsu := by decide
    w := ![![-104100, -5300, 1100], ![-25300, -1800, 200]]
    hw := by decide
    g := ![![![1641252, -782126583, -35554598], ![-7460117, 3555459892, 0]], ![![-692758, 330115420, 15006677], ![3148839, -1500667747, 0]]]
    h := ![![![-5208567, 132445, -371], ![-11921808, 38224, 0]], ![![-1265641, 32176, -90], ![-2896906, 9272, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {100} * I103N1 =  Ideal.span {B.equivFun.symm ![-1041, -53, 11]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E103RS1 


noncomputable def E109RS0 : RelationCertificate Table 4 ![![109, 0, 0], ![0, 1, 0]]
  ![109, -39, -7] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![436, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![436, -156, -28], ![1744, -228, -60]]
    hw := by decide
    g := ![![![-1115, 494, -54], ![-433, 30, 0]], ![![80, -57, -8], ![26, 45, 0]]]
    h := ![![![1, 0, 0], ![-39, -7, 0]], ![![4, -1, 0], ![52, -15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {4} * I109N0 =  Ideal.span {B.equivFun.symm ![109, -39, -7]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E109RS0 


noncomputable def E127RS1 : RelationCertificate Table 20 ![![127, 0, 0], ![-37, 1, 0]]
  ![-2687, -71, 37] ![![20, 0, 0], ![2, 1, 0]] where
    su := ![![2540, 0, 0], ![-740, 20, 0]]
    hsu := by decide
    w := ![![-53740, -1420, 740], ![-13440, -1460, 40]]
    hw := by decide
    g := ![![![3631, -1124, 125], ![313, 59, 0]], ![![-1277, 392, -45], ![-96, 1, 0]]]
    h := ![![![-2169249, 62819, -113], ![-7445728, 14388, 0]], ![![-542314, 15730, -29], ![-1861438, 3685, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {20} * I127N1 =  Ideal.span {B.equivFun.symm ![-2687, -71, 37]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 5 ![![131, 0, 0], ![37, 1, 0]]
  ![-47, 9, 2] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![655, 0, 0], ![185, 5, 0]]
    hsu := by decide
    w := ![![-235, 45, 10], ![-530, 45, 15]]
    hw := by decide
    g := ![![![9737, -140540, -72681], ![-24208, 363414, 0]], ![![2891, -41781, -21608], ![-7197, 108042, 0]]]
    h := ![![![-5384, -183, -1], ![19061, 133, 0]], ![![-12108, -365, -1], ![42866, 134, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {5} * I131N1 =  Ideal.span {B.equivFun.symm ![-47, 9, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E131RS1 


noncomputable def E137RS0 : RelationCertificate Table 25 ![![137, 0, 0], ![59, 1, 0]]
  ![-727, 34, 17] ![![25, 0, 0], ![-3, 1, 0]] where
    su := ![![3425, 0, 0], ![1475, 25, 0]]
    hsu := by decide
    w := ![![-18175, 850, 425], ![-1525, -200, 0]]
    hw := by decide
    g := ![![![-16169, -3449971, 1151794], ![-136040, -28794714, 0]], ![![-6933, -1477356, 493225], ![-58262, -12330574, 0]]]
    h := ![![![-650063, -13857, -48], ![1509456, 6593, 0]], ![![-54631, -1162, -4], ![126854, 548, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {25} * I137N0 =  Ideal.span {B.equivFun.symm ![-727, 34, 17]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 25 ![![137, 0, 0], ![-30, 1, 0]]
  ![-63, 21, -2] ![![25, 0, 0], ![-3, 1, 0]] where
    su := ![![3425, 0, 0], ![-750, 25, 0]]
    hsu := by decide
    w := ![![-1575, 525, -50], ![625, -200, 25]]
    hw := by decide
    g := ![![![12, 625, -209], ![27, 5220, 0]], ![![-1, -135, 45], ![5, -1124, 0]]]
    h := ![![![-579, 49, -1], ![-2642, 135, 0]], ![![245, -8, 0], ![1118, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {25} * I137N1 =  Ideal.span {B.equivFun.symm ![-63, 21, -2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E137RS1 
