import IdealArithmetic.Examples.NF3_1_181804_1.PrimesBelow3_1_181804_1F2
import IdealArithmetic.Examples.NF3_1_181804_1.ClassGroupData3_1_181804_1

set_option linter.all false

noncomputable section


noncomputable def E83RS0 : RelationCertificate Table 297 ![![83, 0, 0], ![17, 1, 0]]
  ![-433, -16, 31] ![![297, 0, 0], ![58, 1, 0]] where
    su := ![![24651, 0, 0], ![5049, 297, 0]]
    hsu := by decide
    w := ![![-128601, -4752, 9207], ![-22572, -1485, 1782]]
    hw := by decide
    g := ![![![-71, 72082, 1243], ![384, -369112, 0]], ![![-15, 15019, 259], ![82, -76908, 0]]]
    h := ![![![-1728301, -106839, -304], ![8438150, 25263, 0]], ![![-303412, -18767, -54], ![1481360, 4488, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N0 : Ideal.span {297} * I83N0 =  Ideal.span {B.equivFun.symm ![-433, -16, 31]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E83RS0 


noncomputable def E83RS1 : RelationCertificate Table 297 ![![83, 0, 0], ![26, 1, 0]]
  ![7795, 1546, 383] ![![297, 0, 0], ![58, 1, 0]] where
    su := ![![24651, 0, 0], ![7722, 297, 0]]
    hsu := by decide
    w := ![![2315115, 459162, 113751], ![483516, 95931, 23760]]
    hw := by decide
    g := ![![![-32153, 50716159, 874426], ![164659, -259704551, 0]], ![![-9680, 15276049, 263383], ![49572, -78224761, 0]]]
    h := ![![![34865, 1470, 9], ![-111000, -364, 0]], ![![7252, 309, 2], ![-23088, -86, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {297} * I83N1 =  Ideal.span {B.equivFun.symm ![7795, 1546, 383]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 9 ![![83, 0, 0], ![40, 1, 0]]
  ![11, 5, 1] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![747, 0, 0], ![360, 9, 0]]
    hsu := by decide
    w := ![![99, 45, 9], ![126, 27, 9]]
    hw := by decide
    g := ![![![-12321, 298664, 75436], ![27715, -678922, 0]], ![![-6708, 162639, 41079], ![15090, -369710, 0]]]
    h := ![![![97, 2, 0], ![-201, 1, 0]], ![![58, 1, 0], ![-120, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {9} * I83N2 =  Ideal.span {B.equivFun.symm ![11, 5, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E83RS2 


noncomputable def E89RS1 : RelationCertificate Table 99 ![![89, 0, 0], ![-19, 1, 0]]
  ![-109, -7, -5] ![![99, 0, 0], ![-41, 1, 0]] where
    su := ![![8811, 0, 0], ![-1881, 99, 0]]
    hsu := by decide
    w := ![![-10791, -693, -495], ![4059, 198, 198]]
    hw := by decide
    g := ![![![-12935, -3629700, 88537], ![-31232, -8765159, 0]], ![![2936, 815377, -19889], ![7089, 1969010, 0]]]
    h := ![![![-217782, 11936, -25], ![-1020131, 2220, 0]], ![![81956, -4484, 9], ![383897, -799, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {99} * I89N1 =  Ideal.span {B.equivFun.symm ![-109, -7, -5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 11 ![![97, 0, 0], ![-33, 1, 0]]
  ![-159, -31, -8] ![![11, 0, 0], ![3, 1, 0]] where
    su := ![![1067, 0, 0], ![-363, 11, 0]]
    hsu := by decide
    w := ![![-1749, -341, -88], ![-1133, -220, -55]]
    hw := by decide
    g := ![![![30051, -1302173, -437395], ![-110176, 4811350, 0]], ![![-9602, 416060, 139753], ![35205, -1537285, 0]]]
    h := ![![![-71349, 2357, -6], ![-209718, 574, 0]], ![![-46231, 1531, -4], ![-135888, 383, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {11} * I97N1 =  Ideal.span {B.equivFun.symm ![-159, -31, -8]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E97RS1 


noncomputable def E101RS0 : RelationCertificate Table 3 ![![101, 0, 0], ![16, 1, 0]]
  ![629, 125, 31] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![303, 0, 0], ![48, 3, 0]]
    hsu := by decide
    w := ![![1887, 375, 93], ![3171, 630, 156]]
    hw := by decide
    g := ![![![-26, 33, 11], ![3, -43, 0]], ![![-7, 5, 2], ![1, -7, 0]]]
    h := ![![![1761, 106, 0], ![-11077, 31, 0]], ![![3005, 181, 0], ![-18903, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {3} * I101N0 =  Ideal.span {B.equivFun.symm ![629, 125, 31]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 9 ![![101, 0, 0], ![31, 1, 0]]
  ![389, 77, 19] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![909, 0, 0], ![279, 9, 0]]
    hsu := by decide
    w := ![![3501, 693, 171], ![3114, 621, 153]]
    hw := by decide
    g := ![![![3, 320, 82], ![41, -740, 0]], ![![1, 102, 26], ![12, -235, 0]]]
    h := ![![![54783, 2041, 9], ![-178474, -890, 0]], ![![48752, 1816, 8], ![-158826, -791, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {9} * I101N1 =  Ideal.span {B.equivFun.symm ![389, 77, 19]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E101RS1 


noncomputable def E101RS2 : RelationCertificate Table 3 ![![101, 0, 0], ![-47, 1, 0]]
  ![1, 4, -1] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![303, 0, 0], ![-141, 3, 0]]
    hsu := by decide
    w := ![![3, 12, -3], ![-81, 9, 3]]
    hw := by decide
    g := ![![![38, 34, 36], ![25, -101, 0]], ![![-17, -17, -17], ![-8, 48, 0]]]
    h := ![![![74, 45, -1], ![159, 100, 0]], ![![-776, 64, -1], ![-1667, 102, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {3} * I101N2 =  Ideal.span {B.equivFun.symm ![1, 4, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS2 


noncomputable def E103RS1 : RelationCertificate Table 3 ![![103, 0, 0], ![-46, 1, 0]]
  ![23, 5, 1] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![309, 0, 0], ![-138, 3, 0]]
    hsu := by decide
    w := ![![69, 15, 3], ![105, 24, 6]]
    hw := by decide
    g := ![![![2, 27, 35], ![11, -103, 0]], ![![-1, -13, -16], ![-3, 47, 0]]]
    h := ![![![3657, -79, 0], ![8188, 1, 0]], ![![5565, -120, 0], ![12460, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {3} * I103N1 =  Ideal.span {B.equivFun.symm ![23, 5, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 33 ![![107, 0, 0], ![26, 1, 0]]
  ![3551, 707, 175] ![![33, 0, 0], ![-8, 1, 0]] where
    su := ![![3531, 0, 0], ![858, 33, 0]]
    hsu := by decide
    w := ![![117183, 23331, 5775], ![-14058, -2805, -693]]
    hw := by decide
    g := ![![![109059, 15719557, -1966648], ![449936, 64899412, 0]], ![![32114, 4628379, -579049], ![132484, 19108624, 0]]]
    h := ![![![2112401, 87709, 250], ![-8693206, -26575, 0]], ![![-253434, -10549, -31], ![1042962, 3296, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {33} * I107N1 =  Ideal.span {B.equivFun.symm ![3551, 707, 175]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 11 ![![109, 0, 0], ![42, 1, 0]]
  ![1525, 303, 75] ![![11, 0, 0], ![3, 1, 0]] where
    su := ![![1199, 0, 0], ![462, 11, 0]]
    hsu := by decide
    w := ![![16775, 3333, 825], ![10725, 2134, 528]]
    hw := by decide
    g := ![![![-12980, 563808, 189384], ![47727, -2083230, 0]], ![![-5589, 242652, 81507], ![20543, -896580, 0]]]
    h := ![![![6991, 182, 1], ![-18107, -34, 0]], ![![4449, 89, 0], ![-11523, 48, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {11} * I109N1 =  Ideal.span {B.equivFun.symm ![1525, 303, 75]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E109RS1 
