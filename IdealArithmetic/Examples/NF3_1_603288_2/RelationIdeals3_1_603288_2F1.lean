import IdealArithmetic.Examples.NF3_1_603288_2.PrimesBelow3_1_603288_2F1
import IdealArithmetic.Examples.NF3_1_603288_2.ClassGroupData3_1_603288_2

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 6400 ![![41, 0, 0], ![5, 1, 0]]
  ![148, -65, 13] ![![6400, 0, 0], ![285, 126, 1]] where
    su := ![![262400, 0, 0], ![32000, 6400, 0]]
    hsu := by decide
    w := ![![947200, -416000, 83200], ![262400, -32000, -12800]]
    hw := by decide
    g := ![![![-77, -111, -97], ![477, 2460, 0]], ![![-90, -49, -12], ![1865, 297, 0]]]
    h := ![![![3808128, 775470, 5539], ![-31226620, -113543, 0]], ![![1057391, 215313, 1534], ![-8670598, -31448, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {6400} * I41N1 =  Ideal.span {B.equivFun.symm ![148, -65, 13]} * (J0 ^ 12*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_12J1_2 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 80 ![![43, 0, 0], ![14, 1, 0]]
  ![-212, -15, -7] ![![80, 0, 0], ![45, 14, 1]] where
    su := ![![3440, 0, 0], ![1120, 80, 0]]
    hsu := by decide
    w := ![![-16960, -1200, -560], ![-25360, -1760, -800]]
    hw := by decide
    g := ![![![-2510806, -314502, -649700], ![-1475383, 1908978, 0]], ![![-927401, -116163, -239979], ![-544986, 705118, 0]]]
    h := ![![![-107620, -9317, -233], ![330532, 5006, 0]], ![![-160897, -13927, -348], ![494161, 7477, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {80} * I43N1 =  Ideal.span {B.equivFun.symm ![-212, -15, -7]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E43RS1 


noncomputable def E47RS0 : RelationCertificate Table 128 ![![47, 0, 0], ![8, 1, 0]]
  ![132, 9, 4] ![![128, 0, 0], ![29, 62, 1]] where
    su := ![![6016, 0, 0], ![1024, 128, 0]]
    hsu := by decide
    w := ![![16896, 1152, 512], ![39808, 3328, 1280]]
    hw := by decide
    g := ![![![17449704, -3614492, -666], ![2202689, 0, -264682]], ![![3172647, -657236, -122], ![400604, 0, -48124]]]
    h := ![![![124, 15, 0], ![-712, 2, 0]], ![![297, 36, 0], ![-1706, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {128} * I47N0 =  Ideal.span {B.equivFun.symm ![132, 9, 4]} * (J0 ^ 13*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_13J1_0 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![-6, 1, 0]]
  ![-6, 1, 0] ![![2, 0, 0], ![15, 1, 1]] where
    su := ![![94, 0, 0], ![-12, 2, 0]]
    hsu := by decide
    w := ![![-12, 2, 0], ![50, -12, -4]]
    hw := by decide
    g := ![![![-4737, -222846, 85705], ![-104091, 0, 11220]], ![![466, 22284, -8571], ![10410, 0, -1122]]]
    h := ![![![-6, 7, -2], ![-46, 47, 0]], ![![35, 0, -2], ![270, 46, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![-6, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 2 ![![47, 0, 0], ![-2, 1, 0]]
  ![-2, 1, 0] ![![2, 0, 0], ![15, 1, 1]] where
    su := ![![94, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-4, 2, 0], ![110, -8, 0]]
    hw := by decide
    g := ![![![-5526, -259987, 99988], ![-121435, 0, 13090]], ![![156, 7428, -2857], ![3470, 0, -374]]]
    h := ![![![-6, 5, -2], ![-140, 47, 0]], ![![175, -87, 0], ![4085, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {2} * I47N2 =  Ideal.span {B.equivFun.symm ![-2, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS2 


noncomputable def E61RS1 : RelationCertificate Table 16 ![![61, 0, 0], ![-12, 1, 0]]
  ![-12, 1, 0] ![![16, 0, 0], ![13, 6, 1]] where
    su := ![![976, 0, 0], ![-192, 16, 0]]
    hsu := by decide
    w := ![![-192, 16, 0], ![-16, -80, 0]]
    hw := by decide
    g := ![![![-4762071, 1697520, 271214], ![-3215649, 0, 140472]], ![![925946, -330079, -52737], ![625280, 0, -27314]]]
    h := ![![![-2364, 209, -2], ![-12016, 61, 0]], ![![11, -1, 0], ![56, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {16} * I61N1 =  Ideal.span {B.equivFun.symm ![-12, 1, 0]} * (J0 ^ 7*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_0 E61RS1 


noncomputable def E71RS1 : RelationCertificate Table 4 ![![71, 0, 0], ![-8, 1, 0]]
  ![-8, 1, 0] ![![4, 0, 0], ![13, 0, 1]] where
    su := ![![284, 0, 0], ![-32, 4, 0]]
    hsu := by decide
    w := ![![-32, 4, 0], ![36, -8, -8]]
    hw := by decide
    g := ![![![-9682, -1210546, 137604], ![2975, 0, 69174]], ![![950, 119070, -13535], ![-292, 0, -6804]]]
    h := ![![![-8, 9, -2], ![-70, 71, 0]], ![![23, 5, -2], ![203, 70, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {4} * I71N1 =  Ideal.span {B.equivFun.symm ![-8, 1, 0]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E71RS1 


noncomputable def E73RS0 : RelationCertificate Table 20 ![![73, 0, 0], ![9, 1, 0]]
  ![-4, 0, 1] ![![20, 0, 0], ![5, 2, 1]] where
    su := ![![1460, 0, 0], ![180, 20, 0]]
    hsu := by decide
    w := ![![-80, 0, 20], ![260, 20, -20]]
    hw := by decide
    g := ![![![-4389954, 635169, -80941], ![-1038011, 664209, 0]], ![![-723619, 104698, -13342], ![-171099, 109485, 0]]]
    h := ![![![-562, -67, -1], ![4558, 37, 0]], ![![1813, 197, -1], ![-14704, 36, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {20} * I73N0 =  Ideal.span {B.equivFun.symm ![-4, 0, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E73RS0 


noncomputable def E73RS1 : RelationCertificate Table 80 ![![73, 0, 0], ![27, 1, 0]]
  ![12, -5, 2] ![![80, 0, 0], ![45, 6, 1]] where
    su := ![![5840, 0, 0], ![2160, 80, 0]]
    hsu := by decide
    w := ![![960, -400, 160], ![1520, -160, 0]]
    hw := by decide
    g := ![![![-67533061, -12471475, -7195869], ![-39012565, 51270224, -23358]], ![![-67533515, -12471560, -7195920], ![-39012907, 51270592, -23358]]]
    h := ![![![15078, 666, 8], ![-40766, -291, 0]], ![![24058, 1053, 12], ![-65045, -438, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {80} * I73N1 =  Ideal.span {B.equivFun.symm ![12, -5, 2]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E73RS1 


noncomputable def E73RS2 : RelationCertificate Table 160 ![![73, 0, 0], ![-36, 1, 0]]
  ![-12, -5, 3] ![![160, 0, 0], ![-35, 30, 1]] where
    su := ![![11680, 0, 0], ![-5760, 160, 0]]
    hsu := by decide
    w := ![![-1920, -800, 480], ![12320, -1760, -480]]
    hw := by decide
    g := ![![![-10148049, 3769442, -4638932], ![2897725, 12322189, 0]], ![![4905722, -1822221, 2242516], ![-1400656, -5956698, 0]]]
    h := ![![![-70284, 2331, -21], ![-142520, 768, 0]], ![![453821, -15001, 133], ![920246, -4856, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {160} * I73N2 =  Ideal.span {B.equivFun.symm ![-12, -5, 3]} * (J0 ^ 8*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_1 E73RS2 


noncomputable def E79RS1 : RelationCertificate Table 32 ![![79, 0, 0], ![-1, 1, 0]]
  ![36, 3, 1] ![![32, 0, 0], ![29, -2, 1]] where
    su := ![![2528, 0, 0], ![-32, 32, 0]]
    hsu := by decide
    w := ![![1152, 96, 32], ![1184, 64, 32]]
    hw := by decide
    g := ![![![3, -1, 0], ![3, 0, 0]], ![![-28, 2, -1], ![31, 0, 0]]]
    h := ![![![2, -1, -1], ![122, 40, 0]], ![![2, -1, -1], ![121, 40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {32} * I79N1 =  Ideal.span {B.equivFun.symm ![36, 3, 1]} * (J0 ^ 10*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_0 E79RS1 
