import IdealArithmetic.Examples.NF3_1_542700_2.PrimesBelow3_1_542700_2F2
import IdealArithmetic.Examples.NF3_1_542700_2.ClassGroupData3_1_542700_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 11 ![![83, 0, 0], ![8, 1, 0]]
  ![-467, -96, -36] ![![11, 0, 0], ![-5, 1, 0]] where
    su := ![![913, 0, 0], ![88, 11, 0]]
    hsu := by decide
    w := ![![-5137, -1056, -396], ![-5225, -1067, -396]]
    hw := by decide
    g := ![![![-39, 502, -612], ![70, 1128, 0]], ![![6, 59, -72], ![10, 132, 0]]]
    h := ![![![-34977, -4420, -36], ![362828, 492, 0]], ![![-35577, -4495, -36], ![369052, 492, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {11} * I83N1 =  Ideal.span {B.equivFun.symm ![-467, -96, -36]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E83RS1 


noncomputable def E83RS2 : RelationCertificate Table 121 ![![83, 0, 0], ![-11, 1, 0]]
  ![-1333, -67, 56] ![![121, 0, 0], ![-49, 1, 0]] where
    su := ![![10043, 0, 0], ![-1331, 121, 0]]
    hsu := by decide
    w := ![![-161293, -8107, 6776], ![77077, 3630, -3146]]
    hw := by decide
    g := ![![![656, 217830, -26674], ![1603, 537936, 0]], ![![-64, -28255, 3460], ![-159, -69776, 0]]]
    h := ![![![-1854681, 171371, -1508], ![-13994290, 20870, 0]], ![![886323, -81887, 716], ![6687652, -9909, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N2 : Ideal.span {121} * I83N2 =  Ideal.span {B.equivFun.symm ![-1333, -67, 56]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E83RS2 


noncomputable def E97RS1 : RelationCertificate Table 847 ![![97, 0, 0], ![5, 1, 0]]
  ![-1117, -91, 58] ![![847, 0, 0], ![-49, 1, 0]] where
    su := ![![82159, 0, 0], ![4235, 847, 0]]
    hsu := by decide
    w := ![![-946099, -77077, 49126], ![66913, 5082, -3388]]
    hw := by decide
    g := ![![![2496623, 36674873437, -4490807068], ![43155912, 633952264430, 0]], ![![254080, 3731899854, -456967964], ![4391955, 64508644251, 0]]]
    h := ![![![-2166, -434, -2], ![41797, 42, 0]], ![![152, 27, -4], ![-2933, 64, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {847} * I97N1 =  Ideal.span {B.equivFun.symm ![-1117, -91, 58]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 7 ![![101, 0, 0], ![-23, 1, 0]]
  ![29, 7, 3] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![707, 0, 0], ![-161, 7, 0]]
    hsu := by decide
    w := ![![203, 49, 21], ![630, 119, 42]]
    hw := by decide
    g := ![![![19, 2, 962349], ![2, -1122742, 0]], ![![-7, -1, -211971], ![2, 247300, 0]]]
    h := ![![![223, 2, -3], ![978, 51, 0]], ![![608, -26, 0], ![2666, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {7} * I101N1 =  Ideal.span {B.equivFun.symm ![29, 7, 3]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E101RS1 


noncomputable def E103RS0 : RelationCertificate Table 847 ![![103, 0, 0], ![43, 1, 0]]
  ![-4157, -49, 115] ![![847, 0, 0], ![-49, 1, 0]] where
    su := ![![87241, 0, 0], ![36421, 847, 0]]
    hsu := by decide
    w := ![![-3520979, -41503, 97405], ![227843, 1694, -5929]]
    hw := by decide
    g := ![![![81, 829627, -101587], ![1370, 14340717, 0]], ![![50, 347124, -42505], ![847, 6000300, 0]]]
    h := ![![![-19205, -533, -11], ![45906, 208, 0]], ![![1235, 22, -1], ![-2952, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N0 : Ideal.span {847} * I103N0 =  Ideal.span {B.equivFun.symm ![-4157, -49, 115]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E103RS0 


noncomputable def E103RS1 : RelationCertificate Table 77 ![![103, 0, 0], ![-33, 1, 0]]
  ![-943, -70, 48] ![![77, 0, 0], ![28, 1, 0]] where
    su := ![![7931, 0, 0], ![-2541, 77, 0]]
    hsu := by decide
    w := ![![-72611, -5390, 3696], ![-16324, -1463, 924]]
    hw := by decide
    g := ![![![-4158009, 996874774, 213647844], ![11434492, -2741814010, 0]], ![![1287199, -308609341, -66140424], ![-3539792, 848802110, 0]]]
    h := ![![![-10870, 364, -6], ![-33899, 111, 0]], ![![-2396, 106, -6], ![-7472, 105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {77} * I103N1 =  Ideal.span {B.equivFun.symm ![-943, -70, 48]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E103RS1 


noncomputable def E103RS2 : RelationCertificate Table 7 ![![103, 0, 0], ![-10, 1, 0]]
  ![103, 21, 8] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![721, 0, 0], ![-70, 7, 0]]
    hsu := by decide
    w := ![![721, 147, 56], ![1680, 343, 126]]
    hw := by decide
    g := ![![![61, 1, -2], ![4, 0, 0]], ![![-10, -1, 2], ![6, -2, 0]]]
    h := ![![![371, -30, -4], ![3811, 70, 0]], ![![840, -83, 0], ![8628, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N2 : Ideal.span {7} * I103N2 =  Ideal.span {B.equivFun.symm ![103, 21, 8]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E103RS2 


noncomputable def E107RS0 : RelationCertificate Table 11 ![![107, 0, 0], ![18, 1, 0]]
  ![37, 2, -2] ![![11, 0, 0], ![-5, 1, 0]] where
    su := ![![1177, 0, 0], ![198, 11, 0]]
    hsu := by decide
    w := ![![407, 22, -22], ![-605, -33, 22]]
    hw := by decide
    g := ![![![-39, -1062, 1282], ![-74, -2350, 0]], ![![-6, -179, 216], ![-12, -396, 0]]]
    h := ![![![35, -10, -4], ![-206, 71, 0]], ![![-89, -11, -2], ![526, 36, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {11} * I107N0 =  Ideal.span {B.equivFun.symm ![37, 2, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 49 ![![107, 0, 0], ![21, 1, 0]]
  ![-97, -77, 31] ![![49, 0, 0], ![7, 1, 0]] where
    su := ![![5243, 0, 0], ![1029, 49, 0]]
    hsu := by decide
    w := ![![-4753, -3773, 1519], ![5831, 294, -245]]
    hw := by decide
    g := ![![![439126, -153677155, -131777045], ![-3073509, 1076179234, 0]], ![![88690, -31036254, -26613363], ![-620701, 217342476, 0]]]
    h := ![![![-836, -45, -1], ![4255, 23, 0]], ![![952, 42, -1], ![-4845, 17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {49} * I107N1 =  Ideal.span {B.equivFun.symm ![-97, -77, 31]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 847 ![![107, 0, 0], ![-39, 1, 0]]
  ![527, 49, 6] ![![847, 0, 0], ![-49, 1, 0]] where
    su := ![![90629, 0, 0], ![-33033, 847, 0]]
    hsu := by decide
    w := ![![446369, 41503, 5082], ![-24563, -1694, 0]]
    hw := by decide
    g := ![![![53, 334865, -41004], ![916, 5788400, 0]], ![![-2, -118433, 14502], ![-35, -2047200, 0]]]
    h := ![![![3352, -85, 0], ![9183, 1, 0]], ![![-118, 42, -6], ![-323, 107, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {847} * I107N2 =  Ideal.span {B.equivFun.symm ![527, 49, 6]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E107RS2 


noncomputable def E109RS1 : RelationCertificate Table 77 ![![109, 0, 0], ![34, 1, 0]]
  ![-61, -14, -8] ![![77, 0, 0], ![28, 1, 0]] where
    su := ![![8393, 0, 0], ![2618, 77, 0]]
    hsu := by decide
    w := ![![-4697, -1078, -616], ![-3388, -693, -308]]
    hw := by decide
    g := ![![![6506351, -1559901246, -334314346], ![-17892480, 4290367443, 0]], ![![2098206, -503049943, -107812474], ![-5770070, 1383593417, 0]]]
    h := ![![![-82279, -2839, -74], ![263775, 1343, 0]], ![![-59380, -2075, -58], ![190364, 1053, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {77} * I109N1 =  Ideal.span {B.equivFun.symm ![-61, -14, -8]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 7 ![![113, 0, 0], ![-30, 1, 0]]
  ![-37, 0, 1] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![791, 0, 0], ![-210, 7, 0]]
    hsu := by decide
    w := ![![-259, 0, 7], ![210, -7, 0]]
    hw := by decide
    g := ![![![1, 0, 811273], ![5, -946485, 0]], ![![0, -1, -199260], ![6, 232470, 0]]]
    h := ![![![-599, 25, -1], ![-2255, 19, 0]], ![![510, -17, 0], ![1920, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {7} * I113N1 =  Ideal.span {B.equivFun.symm ![-37, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E113RS1 


noncomputable def E127RS0 : RelationCertificate Table 121 ![![127, 0, 0], ![19, 1, 0]]
  ![-13, -12, 1] ![![121, 0, 0], ![-49, 1, 0]] where
    su := ![![15367, 0, 0], ![2299, 121, 0]]
    hsu := by decide
    w := ![![-1573, -1452, 121], ![847, 605, -121]]
    hw := by decide
    g := ![![![5252003, 1826612873, -223680007], ![12969228, 4510880140, 0]], ![![937424, 326019527, -39923101], ![2314863, 805115870, 0]]]
    h := ![![![-22554, -1222, -11], ![150755, 233, 0]], ![![12124, 654, 5], ![-81039, -106, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {121} * I127N0 =  Ideal.span {B.equivFun.symm ![-13, -12, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 7 ![![127, 0, 0], ![30, 1, 0]]
  ![-23, 0, 1] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![889, 0, 0], ![210, 7, 0]]
    hsu := by decide
    w := ![![-161, 0, 7], ![210, 7, 0]]
    hw := by decide
    g := ![![![1, 0, 1325], ![5, -1546, 0]], ![![0, 0, 324], ![1, -378, 0]]]
    h := ![![![-3389, -138, -5], ![14346, 106, 0]], ![![4410, 147, 0], ![-18668, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {7} * I127N1 =  Ideal.span {B.equivFun.symm ![-23, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 539 ![![127, 0, 0], ![-49, 1, 0]]
  ![5657, 315, -249] ![![539, 0, 0], ![105, 1, 0]] where
    su := ![![68453, 0, 0], ![-26411, 539, 0]]
    hsu := by decide
    w := ![![3049123, 169785, -134211], ![541695, 31262, -24255]]
    hw := by decide
    g := ![![![641, -2061189, -117783], ![-3324, 10580795, 0]], ![![-377, 794687, 45411], ![1944, -4079410, 0]]]
    h := ![![![194238591, -4358001, 48237], ![503434600, -1021058, 0]], ![![34507379, -774182, 8565], ![89437472, -181300, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {539} * I127N2 =  Ideal.span {B.equivFun.symm ![5657, 315, -249]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E127RS2 


noncomputable def E137RS1 : RelationCertificate Table 121 ![![137, 0, 0], ![-27, 1, 0]]
  ![5693, 1169, 437] ![![121, 0, 0], ![-49, 1, 0]] where
    su := ![![16577, 0, 0], ![-3267, 121, 0]]
    hsu := by decide
    w := ![![688853, 141449, 52877], ![-187187, -38478, -14399]]
    hw := by decide
    g := ![![![4871519, 1694284322, -207475561], ![12029620, 4184090456, 0]], ![![-922449, -320825651, 39287079], ![-2277870, -792289420, 0]]]
    h := ![![![88639, -3371, 25], ![449550, -498, 0]], ![![-24061, 943, -13], ![-122030, 277, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {121} * I137N1 =  Ideal.span {B.equivFun.symm ![5693, 1169, 437]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E137RS1 
