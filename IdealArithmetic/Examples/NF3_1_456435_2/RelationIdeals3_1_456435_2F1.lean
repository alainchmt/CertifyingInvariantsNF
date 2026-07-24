import IdealArithmetic.Examples.NF3_1_456435_2.PrimesBelow3_1_456435_2F1
import IdealArithmetic.Examples.NF3_1_456435_2.ClassGroupData3_1_456435_2

set_option linter.all false

noncomputable section


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![-19, 1, 0]]
  ![151, -43, 22] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![94, 0, 0], ![-38, 2, 0]]
    hsu := by decide
    w := ![![302, -86, 44], ![3324, 396, -410]]
    hw := by decide
    g := ![![![-12562, -3086, -2441], ![-1543, 0, -141]], ![![-2722, -76, 273], ![-38, 0, 60]]]
    h := ![![![18715, -186687, 93466], ![-11514, -549110, 0]], ![![203948, -2035148, 1018909], ![-125702, -5986116, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![151, -43, 22]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS1 


noncomputable def E53RS0 : RelationCertificate Table 10 ![![53, 0, 0], ![5, 1, 0]]
  ![-637, -39, 54] ![![10, 0, 0], ![-4, 1, 0]] where
    su := ![![530, 0, 0], ![50, 10, 0]]
    hsu := by decide
    w := ![![-6370, -390, 540], ![10840, 320, -690]]
    hw := by decide
    g := ![![![-12140802383, 6622266191, -57392952755], ![5518547576, 71741190183, -1007]], ![![-916286598, 499793695, -4331543095], ![416494020, 5414428848, -76]]]
    h := ![![![-386854, -1571076, -1572322], ![-66131, 10416640, 0]], ![![658971, 2676195, 2678319], ![112673, -17743872, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {10} * I53N0 =  Ideal.span {B.equivFun.symm ![-637, -39, 54]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 4 ![![53, 0, 0], ![21, 1, 0]]
  ![-37339, -8037, -3544] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![212, 0, 0], ![84, 4, 0]]
    hsu := by decide
    w := ![![-149356, -32148, -14176], ![-640072, -137772, -60752]]
    hw := by decide
    g := ![![![-2925, 70, 28], ![-1441, 0, 76]], ![![-1195, 16, 16], ![-590, 0, 32]]]
    h := ![![![-10490123, -159840009, -53325128], ![-7172280, 353278530, 0]], ![![-44955857, -685001694, -228527284], ![-30737253, 1513991358, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {4} * I53N1 =  Ideal.span {B.equivFun.symm ![-37339, -8037, -3544]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 25 ![![53, 0, 0], ![-26, 1, 0]]
  ![-1272, -274, -121] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![1325, 0, 0], ![-650, 25, 0]]
    hsu := by decide
    w := ![![-31800, -6850, -3025], ![-20575, -4425, -1950]]
    hw := by decide
    g := ![![![-224189, -449410, -900971], ![-26939, 2815540, 0]], ![![97594, 195625, 392187], ![11743, -1225588, 0]]]
    h := ![![![112, -1974, 683], ![-72, -4540, 0]], ![![87, -1278, 442], ![-17, -2938, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {25} * I53N2 =  Ideal.span {B.equivFun.symm ![-1272, -274, -121]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E53RS2 


noncomputable def E59RS0 : RelationCertificate Table 25 ![![59, 0, 0], ![-29, 1, 0]]
  ![-46, -7, -3] ![![25, 0, 0], ![1, 1, 0]] where
    su := ![![1475, 0, 0], ![-725, 25, 0]]
    hsu := by decide
    w := ![![-1150, -175, -75], ![-525, -125, -50]]
    hw := by decide
    g := ![![![-54, -100, -199], ![16, 622, 0]], ![![25, 47, 96], ![22, -300, 0]]]
    h := ![![![4, -75, 23], ![-2, -170, 0]], ![![11, -33, 10], ![18, -74, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {25} * I59N0 =  Ideal.span {B.equivFun.symm ![-46, -7, -3]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 10 ![![59, 0, 0], ![-26, 1, 0]]
  ![9, 3, 2] ![![10, 0, 0], ![-4, 1, 0]] where
    su := ![![590, 0, 0], ![-260, 10, 0]]
    hsu := by decide
    w := ![![90, 30, 20], ![280, 40, 10]]
    hw := by decide
    g := ![![![1069227467, -583204278, 5054457818], ![-486011413, -6318073254, -1121]], ![![-489305294, 266888898, -2313046611], ![222411010, 2891308713, 513]]]
    h := ![![![4459, -66803, 23254], ![-3074, -171498, 0]], ![![13938, -209007, 72755], ![-9647, -536568, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {10} * I59N1 =  Ideal.span {B.equivFun.symm ![9, 3, 2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 4 ![![59, 0, 0], ![-4, 1, 0]]
  ![125, 27, 12] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![236, 0, 0], ![-16, 4, 0]]
    hsu := by decide
    w := ![![500, 108, 48], ![2164, 464, 204]]
    hw := by decide
    g := ![![![1606003, 18520, -12970], ![807634, 0, -51865]], ![![-87610, -1010, 708], ![-44054, 0, 2829]]]
    h := ![![![43195, -21651, 173652], ![-3246, -1280682, 0]], ![![186943, -93706, 751593], ![-14222, -5542992, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {4} * I59N2 =  Ideal.span {B.equivFun.symm ![125, 27, 12]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E59RS2 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![17, 1, 0]]
  ![91, 3, -6] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![122, 0, 0], ![34, 2, 0]]
    hsu := by decide
    w := ![![182, 6, -12], ![-924, -2, 42]]
    hw := by decide
    g := ![![![169792, 14923, -3252], ![7462, 0, -2187]], ![![75488, 6636, -1443], ![3320, 0, -972]]]
    h := ![![![-4896, -55178, -22086], ![-2239, 168405, 0]], ![![24849, 280612, 112321], ![11567, -856445, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![91, 3, -6]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS1 


noncomputable def E73RS1 : RelationCertificate Table 4 ![![73, 0, 0], ![-17, 1, 0]]
  ![-17, 1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![292, 0, 0], ![-68, 4, 0]]
    hsu := by decide
    w := ![![-68, 4, 0], ![-32, -12, 8]]
    hw := by decide
    g := ![![![-2918, -34, 23], ![-1467, 0, 94]], ![![620, 7, -5], ![312, 0, -20]]]
    h := ![![![-3768, 28500, -16296], ![1315, 148701, 0]], ![![-1745, 13218, -7558], ![621, 68967, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {4} * I73N1 =  Ideal.span {B.equivFun.symm ![-17, 1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 5 ![![79, 0, 0], ![-28, 1, 0]]
  ![36, 7, 3] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![395, 0, 0], ![-140, 5, 0]]
    hsu := by decide
    w := ![![180, 35, 15], ![515, 115, 50]]
    hw := by decide
    g := ![![![243561, 517537, 1095965], ![152221, -684978, 0]], ![![-85633, -181959, -385325], ![-53514, 240828, 0]]]
    h := ![![![9090, -135054, 43237], ![-4852, -426965, 0]], ![![25913, -386040, 123590], ![-14067, -1220450, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {5} * I79N1 =  Ideal.span {B.equivFun.symm ![36, 7, 3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E79RS1 
