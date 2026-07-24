import IdealArithmetic.Examples.NF3_1_538412_3.PrimesBelow3_1_538412_3F0
import IdealArithmetic.Examples.NF3_1_538412_3.ClassGroupData3_1_538412_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 5 ![![2, 0, 0], ![-7, -1, 1]]
  ![-137, 1, 5] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![10, 0, 0], ![-35, -5, 5]]
    hsu := by decide
    w := ![![-685, 5, 25], ![875, -85, 15]]
    hw := by decide
    g := ![![![84, 18, 17], ![-12, 0, 3]], ![![644, 84, 28], ![-107, 0, -14]]]
    h := ![![![-6407, 10894, -5302], ![14335, 0, -1242]], ![![8918, -15163, 7380], ![-19941, 0, 1728]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {5} * I2N0 =  Ideal.span {B.equivFun.symm ![-137, 1, 5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![-2, 1, 0]]
  ![-66052, -8369, -6635] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![125, 0, 0], ![-50, 25, 0]]
    hsu := by decide
    w := ![![-1651300, -209225, -165875], ![-1229450, -155775, -123500]]
    hw := by decide
    g := ![![![3980311204, -4075080531, -20280633335], ![473846582, 50701583331, 5]], ![![-1592124328, 1630032012, 8112252336], ![-189538605, -20280630834, -2]]]
    h := ![![![-11560, -2499, -1327], ![4126, 0, 0]], ![![-8606, -1861, -988], ![3074, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![-66052, -8369, -6635]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![5, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![2288, 257, 16], ![-405, 0, -80]], ![![-571, -65, -4], ![106, 0, 20]]]
    h := ![![![2288, 257, 16], ![-405, 0, -80]], ![![-571, -65, -4], ![106, 0, 20]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 25 ![![7, 0, 0], ![0, 1, 0]]
  ![-1791, -227, -180] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![175, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![-44775, -5675, -4500], ![-33350, -4225, -3350]]
    hw := by decide
    g := ![![![75293783, -77086502, -383639792], ![8963557, 959099479, 2]], ![![75287258, -77079822, -383606558], ![8962771, 959016392, 2]]]
    h := ![![![87759, 86222, -440100], ![12323, 308052, 0]], ![![65366, 64221, -327802], ![9180, 229448, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {25} * I7N0 =  Ideal.span {B.equivFun.symm ![-1791, -227, -180]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 25 ![![11, 0, 0], ![4, 1, 0]]
  ![-56, -7, -5] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![275, 0, 0], ![100, 25, 0]]
    hsu := by decide
    w := ![![-1400, -175, -125], ![-950, -125, -100]]
    hw := by decide
    g := ![![![17323286, -18108526, -90017351], ![2047396, 225007928, 59082]], ![![7251604, -7580314, -37681682], ![857065, 94189366, 24732]]]
    h := ![![![7238, -8106, -39665], ![1897, 43631, 0]], ![![4900, -5488, -26854], ![1285, 29539, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {25} * I11N0 =  Ideal.span {B.equivFun.symm ![-56, -7, -5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 25 ![![11, 0, 0], ![-3, 1, 0]]
  ![179, 38, -30] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![275, 0, 0], ![-75, 25, 0]]
    hsu := by decide
    w := ![![4475, 950, -750], ![-3800, -75, 200]]
    hw := by decide
    g := ![![![-6099163, 6244434, 31076954], ![-726072, -77692392, -24]], ![![1014263, -1038543, -5168506], ![120766, 12921240, 4]]]
    h := ![![![-1076, -2762, 5520], ![45, -6075, 0]], ![![942, 2414, -4822], ![-32, 5305, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {25} * I11N1 =  Ideal.span {B.equivFun.symm ![179, 38, -30]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 25 ![![11, 0, 0], ![-1, 1, 0]]
  ![-1191, 48, 20] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![275, 0, 0], ![-25, 25, 0]]
    hsu := by decide
    w := ![![-29775, 1200, 500], ![-1900, -875, 600]]
    hw := by decide
    g := ![![![-7375495, 7281725, 36314680], ![-888808, -90812423, 42563]], ![![-238787, 234787, 1171352], ![-28803, -2929433, 1373]]]
    h := ![![![-596071, -887912, 2967760], ![-26522, -3264534, 0]], ![![-36139, -53837, 179934], ![-1603, -197925, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {25} * I11N2 =  Ideal.span {B.equivFun.symm ![-1191, 48, 20]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS2 


noncomputable def E17RS1 : RelationCertificate Table 25 ![![17, 0, 0], ![-2, 1, 0]]
  ![-506, 43, -5] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![425, 0, 0], ![-50, 25, 0]]
    hsu := by decide
    w := ![![-12650, 1075, -125], ![-2850, -475, 400]]
    hw := by decide
    g := ![![![-35988, 36156, 180177], ![-4301, -450542, 67]], ![![2496, -2722, -13466], ![302, 33624, -5]]]
    h := ![![![201152, 402364, -1005905], ![7, 1710038, 0]], ![![43908, 87828, -219572], ![1, 373274, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {25} * I17N1 =  Ideal.span {B.equivFun.symm ![-506, 43, -5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 5 ![![19, 0, 0], ![-5, 1, 0]]
  ![-29, 2, 0] ![![5, 0, 0], ![-1, 1, 0]] where
    su := ![![95, 0, 0], ![-25, 5, 0]]
    hsu := by decide
    w := ![![-145, 10, 0], ![25, -35, 20]]
    hw := by decide
    g := ![![![-1643, -184, -10], ![292, 0, 58]], ![![180, 20, 2], ![-29, 0, -6]]]
    h := ![![![-4061, -14506, 20700], ![306, -39330, 0]], ![![765, 2721, -3884], ![-46, 7380, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {5} * I19N1 =  Ideal.span {B.equivFun.symm ![-29, 2, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E31RS1 : RelationCertificate Table 25 ![![31, 0, 0], ![10, 1, 0]]
  ![622093, 78821, 62490] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![775, 0, 0], ![250, 25, 0]]
    hsu := by decide
    w := ![![15552325, 1970525, 1562250], ![11579250, 1467125, 1163150]]
    hw := by decide
    g := ![![![-331360557, 339251007, 1688365394], ![-39447630, -4220913391, -124]], ![![-101545938, 103964027, 517402292], ![-12088776, -1293505719, -38]]]
    h := ![![![15850533, -67214195, -83900160], ![2944906, 260096745, 0]], ![![11801280, -50043319, -62466604], ![2192574, 193651125, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {25} * I31N1 =  Ideal.span {B.equivFun.symm ![622093, 78821, 62490]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E31RS1 
