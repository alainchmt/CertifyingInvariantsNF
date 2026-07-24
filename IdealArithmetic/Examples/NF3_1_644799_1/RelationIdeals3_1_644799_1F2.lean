import IdealArithmetic.Examples.NF3_1_644799_1.PrimesBelow3_1_644799_1F2
import IdealArithmetic.Examples.NF3_1_644799_1.ClassGroupData3_1_644799_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 55 ![![83, 0, 0], ![10, 1, 0]]
  ![103, 2, -7] ![![55, 0, 0], ![3, 4, 1]] where
    su := ![![4565, 0, 0], ![550, 55, 0]]
    hsu := by decide
    w := ![![5665, 110, -385], ![4950, 495, 55]]
    hw := by decide
    g := ![![![91820, 1847, -21467], ![4777, 30150, 0]], ![![11020, 221, -2576], ![579, 3618, 0]]]
    h := ![![![-18, 24, 28], ![82, -259, 0]], ![![-3, -4, -4], ![45, 37, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {55} * I83N0 =  Ideal.span {B.equivFun.symm ![103, 2, -7]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 5 ![![83, 0, 0], ![30, 1, 0]]
  ![-83, 1, 8] ![![5, 0, 0], ![-2, -1, 1]] where
    su := ![![415, 0, 0], ![150, 5, 0]]
    hsu := by decide
    w := ![![-415, 5, 40], ![565, -60, -105]]
    hw := by decide
    g := ![![![1549, -307, 232], ![-511, 0, 0]], ![![352, -69, 52], ![-113, 0, 0]]]
    h := ![![![-3595, 36310, 11668], ![-817, -107604, 0]], ![![4861, -49565, -15927], ![1243, 146880, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {5} * I83N1 =  Ideal.span {B.equivFun.symm ![-83, 1, 8]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 6875 ![![83, 0, 0], ![-41, 1, 0]]
  ![148, 8, 5] ![![6875, 0, 0], ![1688, 454, 1]] where
    su := ![![570625, 0, 0], ![-281875, 6875, 0]]
    hsu := by decide
    w := ![![1017500, 55000, 34375], ![-116875, 75625, 48125]]
    hw := by decide
    g := ![![![-858, -343, -386], ![4079, 648, 0]], ![![-1661, -392, 187], ![6480, -316, 0]]]
    h := ![![![93, 1343, -281], ![-5, 2592, 0]], ![![-2, -210, 44], ![26, -405, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {6875} * I83N2 =  Ideal.span {B.equivFun.symm ![148, 8, 5]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E83RS2 


noncomputable def E89RS1 : RelationCertificate Table 625 ![![89, 0, 0], ![-27, 1, 0]]
  ![-1099, 128, -81] ![![625, 0, 0], ![-187, -171, 1]] where
    su := ![![55625, 0, 0], ![-16875, 625, 0]]
    hsu := by decide
    w := ![![-686875, 80000, -50625], ![-1902500, 223125, -141250]]
    hw := by decide
    g := ![![![164, 160, -1], ![589, 0, 0]], ![![172, 154, -1], ![562, 0, 0]]]
    h := ![![![-31451, -321592, 99783], ![6008, -986752, 0]], ![![-87151, -890754, 276382], ![16519, -2733136, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {625} * I89N1 =  Ideal.span {B.equivFun.symm ![-1099, 128, -81]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 1375 ![![97, 0, 0], ![-15, 1, 0]]
  ![152, -23, -35] ![![1375, 0, 0], ![-312, 79, 1]] where
    su := ![![133375, 0, 0], ![-20625, 1375, 0]]
    hsu := by decide
    w := ![![209000, -31625, -48125], ![396000, 20625, -13750]]
    hw := by decide
    g := ![![![-103661110, -129041592, 195018177], ![16250318, -375582976, 0]], ![![14577648, 18146397, -27424432], ![-2283866, 52816356, 0]]]
    h := ![![![10145, 58294, -30857], ![-919, 332566, 0]], ![![19167, 110186, -58324], ![-1793, 628602, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {1375} * I97N1 =  Ideal.span {B.equivFun.symm ![152, -23, -35]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 11 ![![101, 0, 0], ![18, 1, 0]]
  ![178, -21, 13] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![1111, 0, 0], ![198, 11, 0]]
    hsu := by decide
    w := ![![1958, -231, 143], ![-2321, 275, -176]]
    hw := by decide
    g := ![![![-3082371, -4170263, 9346006], ![181321, -11422895, 0]], ![![-583509, -789451, 1769244], ![34326, -2162409, 0]]]
    h := ![![![401660, -2190107, -1231657], ![49906, 13821930, 0]], ![![-476147, 2596155, 1460008], ![-59054, -16384536, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {11} * I101N1 =  Ideal.span {B.equivFun.symm ![178, -21, 13]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 1375 ![![103, 0, 0], ![-20, 1, 0]]
  ![-2054, 238, -151] ![![1375, 0, 0], ![-312, 79, 1]] where
    su := ![![141625, 0, 0], ![-27500, 1375, 0]]
    hsu := by decide
    w := ![![-2824250, 327250, -207625], ![2421375, -283250, 178750]]
    hw := by decide
    g := ![![![49877116, 62088699, -93833605], ![-7817746, 180712920, 0]], ![![-6879545, -8563973, 12942566], ![1078562, -24925920, 0]]]
    h := ![![![12654, 95085, -38893], ![-1493, 445092, 0]], ![![-10825, -81525, 33346], ![1405, -381612, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {1375} * I103N1 =  Ideal.span {B.equivFun.symm ![-2054, 238, -151]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 3125 ![![107, 0, 0], ![37, 1, 0]]
  ![-758, -54, 13] ![![3125, 0, 0], ![-812, 1079, 1]] where
    su := ![![334375, 0, 0], ![115625, 3125, 0]]
    hsu := by decide
    w := ![![-2368750, -168750, 40625], ![-1390625, -643750, -493750]]
    hw := by decide
    g := ![![![368, -659, -11], ![1956, 0, 0]], ![![371, -534, -3], ![1558, 0, 0]]]
    h := ![![![-7995, 100345, 25799], ![-1769, -306720, 0]], ![![-4668, 58623, 15071], ![-1042, -179195, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {3125} * I107N0 =  Ideal.span {B.equivFun.symm ![-758, -54, 13]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 34375 ![![107, 0, 0], ![-31, 1, 0]]
  ![-113, 26, 8] ![![34375, 0, 0], ![-13312, 1079, 1]] where
    su := ![![3678125, 0, 0], ![-1065625, 34375, 0]]
    hsu := by decide
    w := ![![-3884375, 893750, 275000], ![68750, -515625, 171875]]
    hw := by decide
    g := ![![![5046, 109, -320], ![12742, 1131, 0]], ![![5456, -592, 92], ![14172, -327, 0]]]
    h := ![![![-766443607, -8875496372, 2420235361], ![139105227, -28773909291, 0]], ![![14989896, 173584423, -47334272], ![-2720543, 562751901, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {34375} * I107N1 =  Ideal.span {B.equivFun.symm ![-113, 26, 8]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 275 ![![107, 0, 0], ![-7, 1, 0]]
  ![31, -34, -35] ![![275, 0, 0], ![113, 4, 1]] where
    su := ![![29425, 0, 0], ![-1925, 275, 0]]
    hsu := by decide
    w := ![![8525, -9350, -9625], ![34100, -3025, -5775]]
    hw := by decide
    g := ![![![-1857, 1331, 480], ![-718, -3404, 0]], ![![26, -84, -29], ![270, 204, 0]]]
    h := ![![![1583832, 4763631, -4763080], ![-59026, 56627725, 0]], ![![6232471, 18745200, -18743028], ![-232436, 222833775, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {275} * I107N2 =  Ideal.span {B.equivFun.symm ![31, -34, -35]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E107RS2 


noncomputable def E113RS1 : RelationCertificate Table 5 ![![113, 0, 0], ![47, 1, 0]]
  ![-67, 8, -5] ![![5, 0, 0], ![-2, -1, 1]] where
    su := ![![565, 0, 0], ![235, 5, 0]]
    hsu := by decide
    w := ![![-335, 40, -25], ![-1435, 165, -105]]
    hw := by decide
    g := ![![![35, -2, -1], ![-11, 0, 0]], ![![18, -1, 0], ![-7, 0, 0]]]
    h := ![![![-4088, 67459, 13490], ![-984, -169375, 0]], ![![-17347, 288957, 57783], ![-4608, -725500, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {5} * I113N1 =  Ideal.span {B.equivFun.symm ![-67, 8, -5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E113RS1 
