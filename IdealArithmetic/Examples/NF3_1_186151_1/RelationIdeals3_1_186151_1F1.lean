import IdealArithmetic.Examples.NF3_1_186151_1.PrimesBelow3_1_186151_1F1
import IdealArithmetic.Examples.NF3_1_186151_1.ClassGroupData3_1_186151_1

set_option linter.all false

noncomputable section


noncomputable def E47RS0 : RelationCertificate Table 9 ![![47, 0, 0], ![23, 1, 0]]
  ![97, 39, 4] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![423, 0, 0], ![207, 9, 0]]
    hsu := by decide
    w := ![![873, 351, 36], ![801, 288, 27]]
    hw := by decide
    g := ![![![43, -206, 71], ![-31, -650, 0]], ![![14, -105, 36], ![-15, -328, 0]]]
    h := ![![![4996, 377, 7], ![-10205, -325, 0]], ![![4574, 336, 6], ![-9343, -279, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {9} * I47N0 =  Ideal.span {B.equivFun.symm ![97, 39, 4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 9 ![![47, 0, 0], ![-19, 1, 0]]
  ![-59, -6, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![423, 0, 0], ![-171, 9, 0]]
    hsu := by decide
    w := ![![-531, -54, 9], ![450, 36, -9]]
    hw := by decide
    g := ![![![14, 101, -34], ![12, 304, 0]], ![![-6, -39, 13], ![-2, -116, 0]]]
    h := ![![![-186, 29, -1], ![-457, 48, 0]], ![![166, -9, 0], ![408, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {9} * I47N1 =  Ideal.span {B.equivFun.symm ![-59, -6, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 9 ![![47, 0, 0], ![-4, 1, 0]]
  ![-1343, -510, -50] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![423, 0, 0], ![-36, 9, 0]]
    hsu := by decide
    w := ![![-12087, -4590, -450], ![-9621, -3663, -360]]
    hw := by decide
    g := ![![![9947, 291058, -98090], ![29028, 882760, 0]], ![![-633, -17570, 5920], ![-1733, -53270, 0]]]
    h := ![![![-1569, 378, -2], ![-18100, 44, 0]], ![![-1243, 301, -2], ![-14338, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {9} * I47N2 =  Ideal.span {B.equivFun.symm ![-1343, -510, -50]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E47RS2 


noncomputable def E53RS0 : RelationCertificate Table 3 ![![53, 0, 0], ![26, 1, 0]]
  ![433, 39, -8] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![159, 0, 0], ![78, 3, 0]]
    hsu := by decide
    w := ![![1299, 117, -24], ![-2184, -183, 39]]
    hw := by decide
    g := ![![![-172, -59, 10], ![-18, -49, 0]], ![![-117, -40, 4], ![-13, -25, 0]]]
    h := ![![![7999, 546, 9], ![-16289, -485, 0]], ![![-13520, -943, -16], ![27532, 861, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {3} * I53N0 =  Ideal.span {B.equivFun.symm ![433, 39, -8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 3 ![![53, 0, 0], ![-23, 1, 0]]
  ![212, 81, 8] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![159, 0, 0], ![-69, 3, 0]]
    hsu := by decide
    w := ![![636, 243, 24], ![2184, 828, 81]]
    hw := by decide
    g := ![![![387, 30, -7], ![10, 0, 0]], ![![-204, -16, 4], ![-4, -1, 0]]]
    h := ![![![16426, -778, 3], ![37842, -151, 0]], ![![56408, -2734, 13], ![129952, -662, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {3} * I53N1 =  Ideal.span {B.equivFun.symm ![212, 81, 8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 3 ![![53, 0, 0], ![-3, 1, 0]]
  ![-44, -6, 1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![159, 0, 0], ![-9, 3, 0]]
    hsu := by decide
    w := ![![-132, -18, 3], ![273, 33, -6]]
    hw := by decide
    g := ![![![5, -1, -15867], ![0, 47600, 0]], ![![-2, -1, 476], ![2, -1428, 0]]]
    h := ![![![-46, 15, 0], ![-798, 1, 0]], ![![107, -32, -1], ![1860, 51, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {3} * I53N2 =  Ideal.span {B.equivFun.symm ![-44, -6, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS2 


noncomputable def E59RS0 : RelationCertificate Table 3 ![![59, 0, 0], ![27, 1, 0]]
  ![244, 27, -5] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![177, 0, 0], ![81, 3, 0]]
    hsu := by decide
    w := ![![732, 81, -15], ![-1365, -141, 27]]
    hw := by decide
    g := ![![![67, 23, 27], ![10, -73, 0]], ![![43, 15, 13], ![5, -34, 0]]]
    h := ![![![9434, 433, 3], ![-20606, -182, 0]], ![![-17614, -873, -8], ![38473, 481, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {3} * I59N0 =  Ideal.span {B.equivFun.symm ![244, 27, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![-15, 1, 0]]
  ![346, 132, 13] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![177, 0, 0], ![-45, 3, 0]]
    hsu := by decide
    w := ![![1038, 396, 39], ![3549, 1347, 132]]
    hw := by decide
    g := ![![![477, 46, 7587], ![17, -22790, 0]], ![![-166, -16, -1410], ![-5, 4240, 0]]]
    h := ![![![524, -29, 0], ![2038, 13, 0]], ![![1757, -112, 1], ![6832, -15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![346, 132, 13]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 3 ![![59, 0, 0], ![-12, 1, 0]]
  ![85, 12, -2] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![177, 0, 0], ![-36, 3, 0]]
    hsu := by decide
    w := ![![255, 36, -6], ![-546, -69, 12]]
    hw := by decide
    g := ![![![-25, -8, 6006], ![0, -18020, 0]], ![![2, 0, -1060], ![1, 3180, 0]]]
    h := ![![![131, 1, -1], ![637, 57, 0]], ![![-250, 21, 0], ![-1214, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {3} * I59N2 =  Ideal.span {B.equivFun.symm ![85, 12, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS2 


noncomputable def E61RS1 : RelationCertificate Table 9 ![![61, 0, 0], ![28, 1, 0]]
  ![40, 12, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![549, 0, 0], ![252, 9, 0]]
    hsu := by decide
    w := ![![360, 108, 9], ![153, 81, 9]]
    hw := by decide
    g := ![![![-10, -97, 32], ![-5, -285, 0]], ![![-373, -11127, 3750], ![-1112, -33749, 0]]]
    h := ![![![288, 10, 0], ![-626, 1, 0]], ![![93, 3, 0], ![-202, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {9} * I61N1 =  Ideal.span {B.equivFun.symm ![40, 12, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 3 ![![67, 0, 0], ![-7, 1, 0]]
  ![22, 9, 1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![201, 0, 0], ![-21, 3, 0]]
    hsu := by decide
    w := ![![66, 27, 3], ![273, 99, 9]]
    hw := by decide
    g := ![![![123, 7, -2], ![4, 0, 0]], ![![-21, -2, 3], ![2, -8, 0]]]
    h := ![![![450, -64, 0], ![4304, 1, 0]], ![![1841, -262, 0], ![17608, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3} * I67N1 =  Ideal.span {B.equivFun.symm ![22, 9, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS1 


noncomputable def E79RS0 : RelationCertificate Table 9 ![![79, 0, 0], ![38, 1, 0]]
  ![-263, -15, 4] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![711, 0, 0], ![342, 9, 0]]
    hsu := by decide
    w := ![![-2367, -135, 36], ![1881, 90, -27]]
    hw := by decide
    g := ![![![-4, 170, -60], ![28, 535, 0]], ![![-3, 81, -29], ![16, 258, 0]]]
    h := ![![![-42141, -1567, -12], ![87602, 952, 0]], ![![33383, 1184, 8], ![-69396, -635, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {9} * I79N0 =  Ideal.span {B.equivFun.symm ![-263, -15, 4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 9 ![![79, 0, 0], ![-29, 1, 0]]
  ![-71, -24, -2] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![711, 0, 0], ![-261, 9, 0]]
    hsu := by decide
    w := ![![-639, -216, -18], ![-333, -153, -18]]
    hw := by decide
    g := ![![![84, 177, -58], ![-1, 508, 0]], ![![-34, -56, 18], ![7, -156, 0]]]
    h := ![![![-1075, 65, -1], ![-2926, 77, 0]], ![![-521, 46, -1], ![-1418, 77, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {9} * I79N1 =  Ideal.span {B.equivFun.symm ![-71, -24, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 9 ![![79, 0, 0], ![-9, 1, 0]]
  ![-214, -30, 5] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![711, 0, 0], ![-81, 9, 0]]
    hsu := by decide
    w := ![![-1926, -270, 45], ![2007, 261, -45]]
    hw := by decide
    g := ![![![41606, 1248464, -420781], ![124851, 3787024, 0]], ![![-4429, -132861, 44779], ![-13285, -403011, 0]]]
    h := ![![![-18118, 2040, -3], ![-159012, 242, 0]], ![![18883, -2116, 2], ![165726, -163, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {9} * I79N2 =  Ideal.span {B.equivFun.symm ![-214, -30, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS2 
