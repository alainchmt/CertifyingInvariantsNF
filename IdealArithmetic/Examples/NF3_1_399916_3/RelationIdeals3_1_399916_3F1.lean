import IdealArithmetic.Examples.NF3_1_399916_3.PrimesBelow3_1_399916_3F1
import IdealArithmetic.Examples.NF3_1_399916_3.ClassGroupData3_1_399916_3

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 11 ![![37, 0, 0], ![-5, 1, 0]]
  ![-5, 30, -9] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![407, 0, 0], ![-55, 11, 0]]
    hsu := by decide
    w := ![![-55, 330, -99], ![-1078, 55, 33]]
    hw := by decide
    g := ![![![2095, 3969, 4015], ![752, -22015, 0]], ![![-255, -553, -562], ![-88, 3094, 0]]]
    h := ![![![40, -207, 83], ![-11, -1540, 0]], ![![619, -3208, 1285], ![-154, -23771, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {11} * I37N1 =  Ideal.span {B.equivFun.symm ![-5, 30, -9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 11 ![![43, 0, 0], ![10, 1, 0]]
  ![-170, -25, -9] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![473, 0, 0], ![110, 11, 0]]
    hsu := by decide
    w := ![![-1870, -275, -99], ![-1463, -220, -77]]
    hw := by decide
    g := ![![![-181589, -381631, -387785], ![-67705, 2132820, 0]], ![![-46062, -96805, -98365], ![-17164, 541008, 0]]]
    h := ![![![20925, 232996, 46647], ![10297, -1002915, 0]], ![![16366, 182238, 36485], ![8056, -784431, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {11} * I43N1 =  Ideal.span {B.equivFun.symm ![-170, -25, -9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 121 ![![53, 0, 0], ![-18, 1, 0]]
  ![-140, 15, 1] ![![121, 0, 0], ![-31, 1, 0]] where
    su := ![![6413, 0, 0], ![-2178, 121, 0]]
    hsu := by decide
    w := ![![-16940, 1815, 121], ![4477, -605, 0]]
    hw := by decide
    g := ![![![27355683, -967037668, 62397525], ![-15000403, -3775050265, 0]], ![![-8872996, 313666071, -20239115], ![4865610, 1224466458, 0]]]
    h := ![![![-723, 16666, -1853], ![607, 49105, 0]], ![![208, -4408, 490], ![-111, -12985, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {121} * I53N1 =  Ideal.span {B.equivFun.symm ![-140, 15, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 11 ![![59, 0, 0], ![17, 1, 0]]
  ![54449, 8190, 2900] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![649, 0, 0], ![187, 11, 0]]
    hsu := by decide
    w := ![![598939, 90090, 31900], ![470888, 70829, 25080]]
    hw := by decide
    g := ![![![164073, 344821, 350420], ![61179, -1927260, 0]], ![![52885, 111109, 112912], ![19722, -621006, 0]]]
    h := ![![![32951, 644558, 75904], ![20474, -2237718, 0]], ![![25909, 506754, 59676], ![16087, -1759302, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {11} * I59N1 =  Ideal.span {B.equivFun.symm ![54449, 8190, 2900]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 121 ![![59, 0, 0], ![28, 1, 0]]
  ![-817429, -122954, -43537] ![![121, 0, 0], ![-31, 1, 0]] where
    su := ![![7139, 0, 0], ![3388, 121, 0]]
    hsu := by decide
    w := ![![-98908909, -14877434, -5267977], ![19905831, 2994145, 1060202]]
    hw := by decide
    g := ![![![966, -35015, 2259], ![-440, -136728, 0]], ![![473, -17278, 1115], ![-228, -67464, 0]]]
    h := ![![![-1176984913, -52083483288, -3721994359], ![-1441339978, 109798811822, 0]], ![![236873125, 10482018543, 749066910], ![290075700, -22097469464, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {121} * I59N2 =  Ideal.span {B.equivFun.symm ![-817429, -122954, -43537]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS2 


noncomputable def E61RS0 : RelationCertificate Table 11 ![![61, 0, 0], ![1, 1, 0]]
  ![70, 9, -6] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![671, 0, 0], ![11, 11, 0]]
    hsu := by decide
    w := ![![770, 99, -66], ![-583, 88, 0]]
    hw := by decide
    g := ![![![234, 337, 336], ![76, -1824, 0]], ![![11, 6, 6], ![11, -30, 0]]]
    h := ![![![64, 63, 126], ![12, -3846, 0]], ![![-1, 0, 0], ![8, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {11} * I61N0 =  Ideal.span {B.equivFun.symm ![70, 9, -6]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 11 ![![61, 0, 0], ![-1, 1, 0]]
  ![45, 16, -7] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![671, 0, 0], ![-11, 11, 0]]
    hsu := by decide
    w := ![![495, 176, -77], ![-748, 77, 11]]
    hw := by decide
    g := ![![![232, 279, 275], ![74, -1480, 0]], ![![6, -4, -4], ![11, 25, 0]]]
    h := ![![![75, -74, 147], ![43, -4487, 0]], ![![-11, 10, -21], ![38, 641, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {11} * I61N1 =  Ideal.span {B.equivFun.symm ![45, 16, -7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E73RS1 : RelationCertificate Table 11 ![![73, 0, 0], ![26, 1, 0]]
  ![-57434, -8639, -3059] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![803, 0, 0], ![286, 11, 0]]
    hsu := by decide
    w := ![![-631774, -95029, -33649], ![-496705, -74712, -26455]]
    hw := by decide
    g := ![![![215, -21, -9], ![45, 16, 0]], ![![64, -8, -7], ![19, 24, 0]]]
    h := ![![![1111507, 37305997, 2870615], ![906982, -104778977, 0]], ![![873872, 29330228, 2256897], ![713082, -82377943, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {11} * I73N1 =  Ideal.span {B.equivFun.symm ![-57434, -8639, -3059]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 
