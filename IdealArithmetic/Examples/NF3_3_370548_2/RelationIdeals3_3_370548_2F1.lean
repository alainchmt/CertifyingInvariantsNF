import IdealArithmetic.Examples.NF3_3_370548_2.PrimesBelow3_3_370548_2F1
import IdealArithmetic.Examples.NF3_3_370548_2.ClassGroupData3_3_370548_2

set_option linter.all false

noncomputable section


noncomputable def E47RS0 : RelationCertificate Table 5 ![![47, 0, 0], ![9, 1, 0]]
  ![-169, -6, 4] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![235, 0, 0], ![45, 5, 0]]
    hsu := by decide
    w := ![![-845, -30, 20], ![890, 35, -20]]
    hw := by decide
    g := ![![![19, 77, -76], ![9, 188, 0]], ![![3, 13, -14], ![6, 35, 0]]]
    h := ![![![-584, -74, -2], ![3031, 49, 0]], ![![584, 65, 0], ![-3030, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {5} * I47N0 =  Ideal.span {B.equivFun.symm ![-169, -6, 4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 5 ![![47, 0, 0], ![19, 1, 0]]
  ![127, 28, -7] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![235, 0, 0], ![95, 5, 0]]
    hsu := by decide
    w := ![![635, 140, -35], ![-1220, -265, 70]]
    hw := by decide
    g := ![![![157, -16, 31], ![-61, -88, 0]], ![![53, -8, 13], ![-20, -36, 0]]]
    h := ![![![240, 5, -1], ![-587, 20, 0]], ![![-500, -49, -2], ![1224, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {5} * I47N1 =  Ideal.span {B.equivFun.symm ![127, 28, -7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 25 ![![53, 0, 0], ![-6, 1, 0]]
  ![-1, 6, 1] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![1325, 0, 0], ![-150, 25, 0]]
    hsu := by decide
    w := ![![-25, 150, 25], ![150, -25, 0]]
    hw := by decide
    g := ![![![33865801, 2170233412, -362175927], ![70553759, 4527199088, 0]], ![![-3993828, -255937981, 42711800], ![-8320476, -533897500, 0]]]
    h := ![![![1, 3, -1], ![9, 27, 0]], ![![18, -3, 0], ![158, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {25} * I53N1 =  Ideal.span {B.equivFun.symm ![-1, 6, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 5 ![![53, 0, 0], ![-1, 1, 0]]
  ![2867, 108, -67] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![265, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![14335, 540, -335], ![-14980, -565, 350]]
    hw := by decide
    g := ![![![15, -96, 103], ![-25, -263, 0]], ![![-5, -1, -1], ![3, 3, 0]]]
    h := ![![![112, -55, -3], ![3069, 46, 0]], ![![-114, 56, 0], ![-3046, 35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {5} * I53N2 =  Ideal.span {B.equivFun.symm ![2867, 108, -67]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS2 


noncomputable def E59RS0 : RelationCertificate Table 5 ![![59, 0, 0], ![-27, 1, 0]]
  ![-983, -37, 23] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![295, 0, 0], ![-135, 5, 0]]
    hsu := by decide
    w := ![![-4915, -185, 115], ![5140, 195, -120]]
    hw := by decide
    g := ![![![-15, 106, -115], ![28, 292, 0]], ![![11, -46, 51], ![-13, -130, 0]]]
    h := ![![![-159340, 6702, -59], ![-348151, 1752, 0]], ![![166720, -6989, 60], ![364276, -1782, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {5} * I59N0 =  Ideal.span {B.equivFun.symm ![-983, -37, 23]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 5 ![![59, 0, 0], ![-22, 1, 0]]
  ![251, 9, -6] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![295, 0, 0], ![-110, 5, 0]]
    hsu := by decide
    w := ![![1255, 45, -30], ![-1330, -55, 30]]
    hw := by decide
    g := ![![![-1889, -27916, 28888], ![-4827, -72226, 0]], ![![650, 9683, -10022], ![1678, 25058, 0]]]
    h := ![![![29243, -1462, 12], ![78413, -357, 0]], ![![-30982, 1585, -16], ![-83076, 475, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {5} * I59N1 =  Ideal.span {B.equivFun.symm ![251, 9, -6]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 5 ![![59, 0, 0], ![-10, 1, 0]]
  ![-1, 1, 1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![295, 0, 0], ![-50, 5, 0]]
    hsu := by decide
    w := ![![-5, 5, 5], ![140, 45, 0]]
    hw := by decide
    g := ![![![-8695, -127091, 131479], ![-21935, -328702, 0]], ![![1322, 19376, -20046], ![3349, 50116, 0]]]
    h := ![![![1, 5, -1], ![6, 30, 0]], ![![52, -5, 0], ![304, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {5} * I59N2 =  Ideal.span {B.equivFun.symm ![-1, 1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS2 


noncomputable def E71RS1 : RelationCertificate Table 25 ![![71, 0, 0], ![12, 1, 0]]
  ![-229, -1, 4] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![1775, 0, 0], ![300, 25, 0]]
    hsu := by decide
    w := ![![-5725, -25, 100], ![3300, -25, -50]]
    hw := by decide
    g := ![![![25, 1189, -198], ![46, 2478, 0]], ![![12, 228, -38], ![23, 476, 0]]]
    h := ![![![-251, -33, -2], ![1466, 73, 0]], ![![108, 9, 0], ![-628, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {25} * I71N1 =  Ideal.span {B.equivFun.symm ![-229, -1, 4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 


noncomputable def E73RS0 : RelationCertificate Table 5 ![![73, 0, 0], ![18, 1, 0]]
  ![-19, -6, -1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![365, 0, 0], ![90, 5, 0]]
    hsu := by decide
    w := ![![-95, -30, -5], ![-100, -55, -10]]
    hw := by decide
    g := ![![![-3, 32, -33], ![13, 82, 0]], ![![0, 11, -12], ![6, 30, 0]]]
    h := ![![![-973, -63, -1], ![3945, 36, 0]], ![![-1028, -75, -2], ![4168, 72, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {5} * I73N0 =  Ideal.span {B.equivFun.symm ![-19, -6, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS0 


noncomputable def E73RS1 : RelationCertificate Table 5 ![![73, 0, 0], ![-36, 1, 0]]
  ![671, 24, -16] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![365, 0, 0], ![-180, 5, 0]]
    hsu := by decide
    w := ![![3355, 120, -80], ![-3550, -145, 80]]
    hw := by decide
    g := ![![![-253, -130, 68], ![78, -130, 0]], ![![152, 69, -32], ![-46, 56, 0]]]
    h := ![![![122747, -4061, 36], ![248885, -1322, 0]], ![![-129806, 4329, -40], ![-263198, 1468, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {5} * I73N1 =  Ideal.span {B.equivFun.symm ![671, 24, -16]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 5 ![![79, 0, 0], ![10, 1, 0]]
  ![-11, -4, 1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![395, 0, 0], ![50, 5, 0]]
    hsu := by decide
    w := ![![-55, -20, 5], ![160, 45, -10]]
    hw := by decide
    g := ![![![5749, 83157, -86023], ![14334, 215057, 0]], ![![792, 11443, -11838], ![1976, 29595, 0]]]
    h := ![![![-29, -8, -1], ![228, 40, 0]], ![![28, -7, -2], ![-218, 78, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {5} * I79N1 =  Ideal.span {B.equivFun.symm ![-11, -4, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 25 ![![79, 0, 0], ![-15, 1, 0]]
  ![583, 127, -33] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![1975, 0, 0], ![-375, 25, 0]]
    hsu := by decide
    w := ![![14575, 3175, -825], ![-11550, -2525, 650]]
    hw := by decide
    g := ![![![43, -251, 41], ![-17, -528, 0]], ![![-9, 7, -1], ![6, 16, 0]]]
    h := ![![![237187, -16301, 65], ![1249146, -2584, 0]], ![![-187908, 12933, -54], ![-989618, 2146, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {25} * I79N2 =  Ideal.span {B.equivFun.symm ![583, 127, -33]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS2 
