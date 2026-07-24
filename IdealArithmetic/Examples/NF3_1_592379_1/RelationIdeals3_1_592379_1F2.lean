import IdealArithmetic.Examples.NF3_1_592379_1.PrimesBelow3_1_592379_1F2
import IdealArithmetic.Examples.NF3_1_592379_1.ClassGroupData3_1_592379_1

set_option linter.all false

noncomputable section


noncomputable def E97RS0 : RelationCertificate Table 28 ![![97, 0, 0], ![-46, 1, 0]]
  ![15, 17, -15] ![![28, 0, 0], ![2, 1, 0]] where
    su := ![![2716, 0, 0], ![-1288, 28, 0]]
    hsu := by decide
    w := ![![420, 476, -420], ![-1260, 784, -28]]
    hw := by decide
    g := ![![![30470, -11722279, -5868567], ![-416459, 164320279, 0]], ![![-14097, 5424469, 2715672], ![192737, -76039000, 0]]]
    h := ![![![233, 34, -1], ![491, 82, 0]], ![![-607, 59, -1], ![-1279, 96, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {28} * I97N0 =  Ideal.span {B.equivFun.symm ![15, 17, -15]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 4 ![![97, 0, 0], ![-6, 1, 0]]
  ![55, 1, 1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![388, 0, 0], ![-24, 4, 0]]
    hsu := by decide
    w := ![![220, 4, 4], ![196, 8, 4]]
    hw := by decide
    g := ![![![-8, 107, 57], ![25, -229, 0]], ![![-1, -6, -3], ![1, 12, 0]]]
    h := ![![![1303, -217, 0], ![21056, 1, 0]], ![![1153, -192, 0], ![18632, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {4} * I97N1 =  Ideal.span {B.equivFun.symm ![55, 1, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E97RS1 


noncomputable def E103RS1 : RelationCertificate Table 28 ![![103, 0, 0], ![-28, 1, 0]]
  ![-9087, -129, -181] ![![28, 0, 0], ![2, 1, 0]] where
    su := ![![2884, 0, 0], ![-784, 28, 0]]
    hsu := by decide
    w := ![![-254436, -3612, -5068], ![-33740, -476, -672]]
    hw := by decide
    g := ![![![143720899, -56626033738, -28348947094], ![-2012092560, 793770518613, 0]], ![![-39534877, 15576740392, 7798253915], ![553488263, -218351109615, 0]]]
    h := ![![![-7480301, 284600, -625], ![-27516497, 64194, 0]], ![![-991903, 37742, -83], ![-3648743, 8525, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {28} * I103N1 =  Ideal.span {B.equivFun.symm ![-9087, -129, -181]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E103RS1 


noncomputable def E107RS1 : RelationCertificate Table 8 ![![107, 0, 0], ![-24, 1, 0]]
  ![-4169, -59, -83] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![856, 0, 0], ![-192, 8, 0]]
    hsu := by decide
    w := ![![-33352, -472, -664], ![1200, 16, 24]]
    hw := by decide
    g := ![![![-131, -4833, 2449], ![-566, -19581, 0]], ![![32, 1098, -557], ![133, 4453, 0]]]
    h := ![![![-902179, 39106, -64], ![-4022041, 6765, 0]], ![![32466, -1400, 2], ![144738, -211, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {8} * I107N1 =  Ideal.span {B.equivFun.symm ![-4169, -59, -83]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 4 ![![109, 0, 0], ![-43, 1, 0]]
  ![11, -15, 5] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![436, 0, 0], ![-172, 4, 0]]
    hsu := by decide
    w := ![![44, -60, 20], ![452, -264, 0]]
    hw := by decide
    g := ![![![-10156, 68398, 35649], ![12025, -142926, 0]], ![![3840, -25859, -13477], ![-4541, 54033, 0]]]
    h := ![![![2229, -50, 0], ![5650, 5, 0]], ![![22077, -557, 1], ![55960, -109, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {4} * I109N0 =  Ideal.span {B.equivFun.symm ![11, -15, 5]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 14 ![![109, 0, 0], ![-39, 1, 0]]
  ![13, -3, 1] ![![14, 0, 0], ![2, 1, 0]] where
    su := ![![1526, 0, 0], ![-546, 14, 0]]
    hsu := by decide
    w := ![![182, -42, 14], ![112, -42, 0]]
    hw := by decide
    g := ![![![-37071, 3707778, 1863159], ![259559, -26084223, 0]], ![![13205, -1320954, -663779], ![-92456, 9292905, 0]]]
    h := ![![![169, -4, 0], ![472, 1, 0]], ![![116, -3, 0], ![324, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {14} * I109N1 =  Ideal.span {B.equivFun.symm ![13, -3, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 56 ![![109, 0, 0], ![-28, 1, 0]]
  ![33, -13, -5] ![![56, 0, 0], ![-26, 1, 0]] where
    su := ![![6104, 0, 0], ![-1568, 56, 0]]
    hsu := by decide
    w := ![![1848, -728, -280], ![-1288, 616, 112]]
    hw := by decide
    g := ![![![-97755315, -14332430947, 551391952], ![-210549854, -30877949341, 0]], ![![25409789, 3725464228, -143324674], ![54728763, 8026181751, 0]]]
    h := ![![![59545, -2240, 4], ![231799, -441, 0]], ![![-41479, 1566, -3], ![-161471, 329, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {56} * I109N2 =  Ideal.span {B.equivFun.symm ![33, -13, -5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E109RS2 


noncomputable def E113RS1 : RelationCertificate Table 56 ![![113, 0, 0], ![-35, 1, 0]]
  ![73, -61, 11] ![![56, 0, 0], ![-26, 1, 0]] where
    su := ![![6328, 0, 0], ![-1960, 56, 0]]
    hsu := by decide
    w := ![![4088, -3416, 616], ![-952, 1120, -336]]
    hw := by decide
    g := ![![![460, 50341, -1934], ![709, 108450, 0]], ![![-130, -15539, 597], ![-197, -33475, 0]]]
    h := ![![![1361, -36, 0], ![4392, 11, 0]], ![![-269, 41, -1], ![-868, 107, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {56} * I113N1 =  Ideal.span {B.equivFun.symm ![73, -61, 11]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 2 ![![131, 0, 0], ![-17, 1, 0]]
  ![15, -7, -1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![262, 0, 0], ![-34, 2, 0]]
    hsu := by decide
    w := ![![30, -14, -2], ![-86, 64, -8]]
    hw := by decide
    g := ![![![1508, 17, -59592], ![9, 119244, 0]], ![![-176, -2, 7580], ![-1, -15167, 0]]]
    h := ![![![133, 9, -1], ![1024, 130, 0]], ![![-345, 37, -1], ![-2656, 127, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {2} * I131N1 =  Ideal.span {B.equivFun.symm ![15, -7, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E131RS1 


noncomputable def E131RS2 : RelationCertificate Table 8 ![![131, 0, 0], ![-15, 1, 0]]
  ![11, -7, 1] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![1048, 0, 0], ![-120, 8, 0]]
    hsu := by decide
    w := ![![88, -56, 8], ![64, -24, -8]]
    hw := by decide
    g := ![![![67, 249, -124], ![21, 1002, 0]], ![![-5, -29, 14], ![5, -113, 0]]]
    h := ![![![76, -5, 0], ![663, 1, 0]], ![![58, 11, -1], ![506, 130, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N2 : Ideal.span {8} * I131N2 =  Ideal.span {B.equivFun.symm ![11, -7, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E131RS2 


noncomputable def E137RS1 : RelationCertificate Table 28 ![![137, 0, 0], ![18, 1, 0]]
  ![4173, 59, 83] ![![28, 0, 0], ![2, 1, 0]] where
    su := ![![3836, 0, 0], ![504, 28, 0]]
    hsu := by decide
    w := ![![116844, 1652, 2324], ![15484, 224, 308]]
    hw := by decide
    g := ![![![0, 161, 80], ![13, -2255, 0]], ![![-1, 22, 11], ![11, -310, 0]]]
    h := ![![![1693749, 96047, 109], ![-12891080, -14850, 0]], ![![224453, 12720, 14], ![-1708306, -1907, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {28} * I137N1 =  Ideal.span {B.equivFun.symm ![4173, 59, 83]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 112 ![![137, 0, 0], ![-20, 1, 0]]
  ![-83, 31, -1] ![![112, 0, 0], ![30, 1, 0]] where
    su := ![![15344, 0, 0], ![-2240, 112, 0]]
    hsu := by decide
    w := ![![-9296, 3472, -112], ![-2576, 896, 0]]
    hw := by decide
    g := ![![![-544, 230144, 7672], ![2017, -859272, 0]], ![![68, -34198, -1140], ![-252, 127681, 0]]]
    h := ![![![-659, 53, -1], ![-4510, 136, 0]], ![![-159, 28, -1], ![-1088, 137, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {112} * I137N2 =  Ideal.span {B.equivFun.symm ![-83, 31, -1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E137RS2 
