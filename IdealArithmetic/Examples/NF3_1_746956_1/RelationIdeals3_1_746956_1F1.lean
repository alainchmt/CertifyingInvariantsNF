import IdealArithmetic.Examples.NF3_1_746956_1.PrimesBelow3_1_746956_1F1
import IdealArithmetic.Examples.NF3_1_746956_1.ClassGroupData3_1_746956_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 9 ![![37, 0, 0], ![9, 1, 0]]
  ![-4, 0, 1] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![333, 0, 0], ![81, 9, 0]]
    hsu := by decide
    w := ![![-36, 0, 9], ![90, -27, 0]]
    hw := by decide
    g := ![![![-41, 220, 304], ![10, -249, 0]], ![![-84, 537, 743], ![30, -608, 0]]]
    h := ![![![-19, 185, 157], ![19, -528, 0]], ![![37, -468, -396], ![-3, 1332, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {9} * I37N0 =  Ideal.span {B.equivFun.symm ![-4, 0, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 9 ![![37, 0, 0], ![-18, 1, 0]]
  ![14, 0, 1] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![333, 0, 0], ![-162, 9, 0]]
    hsu := by decide
    w := ![![126, 0, 9], ![162, -9, 0]]
    hw := by decide
    g := ![![![-32, 210, 291], ![16, -238, 0]], ![![12, -96, -132], ![-1, 108, 0]]]
    h := ![![![254, 3496, -2747], ![8, 9240, 0]], ![![330, 4620, -3630], ![-1, 12210, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {9} * I37N1 =  Ideal.span {B.equivFun.symm ![14, 0, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E37RS1 


noncomputable def E47RS1 : RelationCertificate Table 9 ![![47, 0, 0], ![14, 1, 0]]
  ![-1, 0, -2] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![423, 0, 0], ![126, 9, 0]]
    hsu := by decide
    w := ![![-9, 0, -18], ![-216, 45, 0]]
    hw := by decide
    g := ![![![-23, -4, -6], ![-4, 4, 0]], ![![-10, -15, -20], ![4, 16, 0]]]
    h := ![![![-342, 5908, 3611], ![46, -15429, 0]], ![![-8121, 142600, 87153], ![663, -372381, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {9} * I47N1 =  Ideal.span {B.equivFun.symm ![-1, 0, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 11 ![![53, 0, 0], ![25, 1, 0]]
  ![3, -2, 0] ![![11, 0, 0], ![3, 1, 0]] where
    su := ![![583, 0, 0], ![275, 11, 0]]
    hsu := by decide
    w := ![![33, -22, 0], ![11, -11, -22]]
    hw := by decide
    g := ![![![-44, 9, 0], ![-9, 0, 4]], ![![-24, 4, 0], ![1, 0, 2]]]
    h := ![![![-39, 434, 165], ![51, -795, 0]], ![![-23, 147, 56], ![38, -270, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {11} * I53N1 =  Ideal.span {B.equivFun.symm ![3, -2, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![-12, 1, 0]]
  ![-95, -3, -4] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![177, 0, 0], ![-36, 3, 0]]
    hsu := by decide
    w := ![![-285, -9, -12], ![-516, -18, -21]]
    hw := by decide
    g := ![![![0, -1, 1], ![2, 0, 0]], ![![2, -2, -4], ![0, 1, 0]]]
    h := ![![![776, 6257, -8603], ![-22, 46143, 0]], ![![1402, 11328, -15575], ![-54, 83538, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![-95, -3, -4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 243 ![![61, 0, 0], ![6, 1, 0]]
  ![-535, -18, -26] ![![243, 0, 0], ![-41, 1, 0]] where
    su := ![![14823, 0, 0], ![1458, 243, 0]]
    hsu := by decide
    w := ![![-130005, -4374, -6318], ![19197, 729, 972]]
    hw := by decide
    g := ![![![-5215582985116, -193499446271951, 57526760000979], ![83701465682, -1270818425476173, 0]], ![![-511331665314, -18970533952457, 5639878432725], ![8206026093, -124590041741107, 0]]]
    h := ![![![-6363, 63126, 69446], ![416, -385112, 0]], ![![977, -9712, -10684], ![-45, 59248, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {243} * I61N1 =  Ideal.span {B.equivFun.symm ![-535, -18, -26]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 11 ![![67, 0, 0], ![15, 1, 0]]
  ![15, 1, 0] ![![11, 0, 0], ![3, 1, 0]] where
    su := ![![737, 0, 0], ![165, 11, 0]]
    hsu := by decide
    w := ![![165, 11, 0], ![44, 22, 11]]
    hw := by decide
    g := ![![![6214092, -1581126, -62614], ![1551020, 0, -688755]], ![![1608352, -409233, -16206], ![401445, 0, -178266]]]
    h := ![![![-39, 455, 264], ![68, -1608, 0]], ![![-17, 115, 67], ![49, -408, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {11} * I67N1 =  Ideal.span {B.equivFun.symm ![15, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 363 ![![71, 0, 0], ![-1, 1, 0]]
  ![-91, 24, 22] ![![363, 0, 0], ![157, 1, 0]] where
    su := ![![25773, 0, 0], ![-363, 363, 0]]
    hsu := by decide
    w := ![![-33033, 8712, 7986], ![-11979, 3267, 3630]]
    hw := by decide
    g := ![![![-13994714, 2244243090, 153334700], ![129950, -5060002743, -3045]], ![![91986, -14767628, -1008977], ![-618, 33295963, 20]]]
    h := ![![![-3150, 9453, 34672], ![231, -223790, 0]], ![![-1142, 3428, 12575], ![116, -81165, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {363} * I71N1 =  Ideal.span {B.equivFun.symm ![-91, 24, 22]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 1089 ![![73, 0, 0], ![-4, 1, 0]]
  ![-1274, -27, -55] ![![1089, 0, 0], ![157, 1, 0]] where
    su := ![![79497, 0, 0], ![-4356, 1089, 0]]
    hsu := by decide
    w := ![![-1387386, -29403, -59895], ![-205821, -4356, -8712]]
    hw := by decide
    g := ![![![2268922369468, -365107089745460, -24945205401070], ![-8160034203, 2469575334737810, -2292]], ![![-122751753894, 19752784928640, 1349569184295], ![441469621, -133607349246930, 124]]]
    h := ![![![24867623, 18662, -274365190], ![-1362353, 1820787165, 0]], ![![3689161, 2768, -40702594], ![-202068, 270117214, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {1089} * I73N1 =  Ideal.span {B.equivFun.symm ![-1274, -27, -55]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 243 ![![79, 0, 0], ![24, 1, 0]]
  ![-146, -9, -13] ![![243, 0, 0], ![-41, 1, 0]] where
    su := ![![19197, 0, 0], ![5832, 243, 0]]
    hsu := by decide
    w := ![![-35478, -2187, -3159], ![4617, 486, 486]]
    hw := by decide
    g := ![![![-177, -7707, 2291], ![187, -50611, 0]], ![![-64, -2432, 723], ![11, -15972, 0]]]
    h := ![![![-2010859, 55520790, 21812196], ![91937, -156651227, 0]], ![![261463, -7219675, -2836360], ![-11889, 20370222, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {243} * I79N1 =  Ideal.span {B.equivFun.symm ![-146, -9, -13]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E79RS1 
