import IdealArithmetic.Examples.NF3_1_603288_2.PrimesBelow3_1_603288_2F2
import IdealArithmetic.Examples.NF3_1_603288_2.ClassGroupData3_1_603288_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 640 ![![83, 0, 0], ![-18, 1, 0]]
  ![-92, 15, 3] ![![640, 0, 0], ![285, 126, 1]] where
    su := ![![53120, 0, 0], ![-11520, 640, 0]]
    hsu := by decide
    w := ![![-58880, 9600, 1920], ![28800, -15360, 4480]]
    hw := by decide
    g := ![![![-214, -111, -17], ![479, 42, 0]], ![![-151, -65, 1], ![338, -4, 0]]]
    h := ![![![-1181836, 68313, -295], ![-5449572, 12244, 0]], ![![579033, -33455, 143], ![2669983, -5931, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {640} * I83N1 =  Ideal.span {B.equivFun.symm ![-92, 15, 3]} * (J0 ^ 12*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_12J1_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 200 ![![89, 0, 0], ![-11, 1, 0]]
  ![-108, 15, 2] ![![200, 0, 0], ![45, 2, 1]] where
    su := ![![17800, 0, 0], ![-2200, 200, 0]]
    hsu := by decide
    w := ![![-21600, 3000, 400], ![-2200, 200, 0]]
    hw := by decide
    g := ![![![-16081080167, -2861196808, -464530148], ![-3649177463, 24149481462, -1779950]], ![![1929729552, 343343609, 55743616], ![437901425, -2897937720, 213594]]]
    h := ![![![-242768, 22400, -60], ![-1964204, 2671, 0]], ![![-24717, 2291, -8], ![-199982, 356, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {200} * I89N1 =  Ideal.span {B.equivFun.symm ![-108, 15, 2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 80 ![![97, 0, 0], ![40, 1, 0]]
  ![-24, 0, 1] ![![80, 0, 0], ![45, 14, 1]] where
    su := ![![7760, 0, 0], ![3200, 80, 0]]
    hsu := by decide
    w := ![![-1920, 0, 80], ![880, -560, 0]]
    hw := by decide
    g := ![![![5153994, 645562, 1333684], ![3028843, -3918699, 0]], ![![2245311, 281237, 581011], ![1319484, -1707156, 0]]]
    h := ![![![-152, -24, -1], ![368, 49, 0]], ![![3, 0, 0], ![-7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {80} * I97N1 =  Ideal.span {B.equivFun.symm ![-24, 0, 1]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 800 ![![101, 0, 0], ![18, 1, 0]]
  ![52, -35, 12] ![![800, 0, 0], ![-35, 14, 1]] where
    su := ![![80800, 0, 0], ![14400, 800, 0]]
    hsu := by decide
    w := ![![41600, -28000, 9600], ![16800, 0, -1600]]
    hw := by decide
    g := ![![![64437296034651, -25774923843585, 12920003979343], ![-3254042863231, -369026739508320, 7756752]], ![![13424436733231, -5369775824485, 2691667507594], ![-677925599354, -76880571070728, 1615990]]]
    h := ![![![559916, 32383, 142], ![-3141748, -7165, 0]], ![![226797, 13104, 56], ![-1272582, -2829, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {800} * I101N1 =  Ideal.span {B.equivFun.symm ![52, -35, 12]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E101RS1 


noncomputable def E103RS1 : RelationCertificate Table 320 ![![103, 0, 0], ![48, 1, 0]]
  ![16, -10, 1] ![![320, 0, 0], ![-35, 62, 1]] where
    su := ![![32960, 0, 0], ![15360, 320, 0]]
    hsu := by decide
    w := ![![5120, -3200, 320], ![6720, 320, -1280]]
    hw := by decide
    g := ![![![-92, -6, -106], ![275, 271, 0]], ![![-53, 12, -51], ![56, 131, 0]]]
    h := ![![![83728, 2632, 37], ![-179666, -1905, 0]], ![![111603, 3478, 48], ![-239481, -2474, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {320} * I103N1 =  Ideal.span {B.equivFun.symm ![16, -10, 1]} * (J0 ^ 10*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_1 E103RS1 


noncomputable def E107RS0 : RelationCertificate Table 3200 ![![107, 0, 0], ![44, 1, 0]]
  ![-884, -55, -29] ![![3200, 0, 0], ![285, 126, 1]] where
    su := ![![342400, 0, 0], ![140800, 3200, 0]]
    hsu := by decide
    w := ![![-2828800, -176000, -92800], ![-771200, -51200, -22400]]
    hw := by decide
    g := ![![![-939, -1729, -1638], ![329, 20799, 0]], ![![-662, -847, -692], ![3124, 8775, 0]]]
    h := ![![![-50873004, -1565245, -18593], ![123713876, 994711, 0]], ![![-13870223, -426749, -5069], ![33729855, 271188, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {3200} * I107N0 =  Ideal.span {B.equivFun.symm ![-884, -55, -29]} * (J0 ^ 10*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_2 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 12800 ![![107, 0, 0], ![-24, 1, 0]]
  ![324, 5, -6] ![![12800, 0, 0], ![-61205, -3278, -4441]] where
    su := ![![1369600, 0, 0], ![-307200, 12800, 0]]
    hsu := by decide
    w := ![![4147200, 64000, -76800], ![-20185600, 550400, -1664000]]
    hw := by decide
    g := ![![![959834271402490133997, -1918798160456519268672, -1092705380039302001056], ![-3719072782692062176287, 385871470933941342732, 328703880]], ![![-207964092137081235922, 415739601431996124798, 236752832341706561571], ![805799102916129467548, -83605485368970405600, -71219174]]]
    h := ![![![118988700, -5156439, 16548], ![530491274, -885321, 0]], ![![-579234163, 25101318, -80548], ![-2582418911, 4309253, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {12800} * I107N1 =  Ideal.span {B.equivFun.symm ![324, 5, -6]} * (J0 ^ 13*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_13J1_2 E107RS1 


noncomputable def E107RS2 : RelationCertificate Table 1600 ![![107, 0, 0], ![-20, 1, 0]]
  ![268, 35, 8] ![![1600, 0, 0], ![-675, 30, 1]] where
    su := ![![171200, 0, 0], ![-32000, 1600, 0]]
    hsu := by decide
    w := ![![428800, 56000, 12800], ![-142400, -20800, -3200]]
    hw := by decide
    g := ![![![-223876660311627512, 1362241696969415308, -117703407240855809], ![119916433257620273, 3136758919718198928, 44511870]], ![![41331075749830238, -251490774825065666, 21729859798306899], ![-22138418447553944, -579093954409381956, -8217576]]]
    h := ![![![9034564, -466187, 1446], ![48334904, -77357, 0]], ![![-3000107, 154825, -482], ![-16050568, 25786, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N2 : Ideal.span {1600} * I107N2 =  Ideal.span {B.equivFun.symm ![268, 35, 8]} * (J0 ^ 7*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_2 E107RS2 


noncomputable def E109RS0 : RelationCertificate Table 20 ![![109, 0, 0], ![54, 1, 0]]
  ![16, -5, 1] ![![20, 0, 0], ![5, 2, 1]] where
    su := ![![2180, 0, 0], ![1080, 20, 0]]
    hsu := by decide
    w := ![![320, -100, 20], ![-340, 140, -20]]
    hw := by decide
    g := ![![![-7274833, 1052574, -134132], ![-1720141, 1100698, 0]], ![![-3817486, 552341, -70386], ![-902650, 577594, 0]]]
    h := ![![![3688, 95, 1], ![-7444, -54, 0]], ![![-4013, -155, -3], ![8100, 163, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {20} * I109N0 =  Ideal.span {B.equivFun.symm ![16, -5, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 20 ![![109, 0, 0], ![-40, 1, 0]]
  ![36, -10, 1] ![![20, 0, 0], ![5, 2, 1]] where
    su := ![![2180, 0, 0], ![-800, 20, 0]]
    hsu := by decide
    w := ![![720, -200, 20], ![-940, 260, -20]]
    hw := by decide
    g := ![![![-3528, 521, -65], ![-831, 542, 0]], ![![1263, -187, 23], ![304, -194, 0]]]
    h := ![![![644, 4, -1], ![1754, 55, 0]], ![![-683, 37, -1], ![-1860, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {20} * I109N1 =  Ideal.span {B.equivFun.symm ![36, -10, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 640 ![![109, 0, 0], ![-14, 1, 0]]
  ![92, -5, 2] ![![640, 0, 0], ![285, 62, 1]] where
    su := ![![69760, 0, 0], ![-8960, 640, 0]]
    hsu := by decide
    w := ![![58880, -3200, 1280], ![42880, 1920, 0]]
    hw := by decide
    g := ![![![-340514242, -772408378, -374611185], ![-227047061, 1932337704, 1395190]], ![![-276, -79, -11], ![594, 52, 0]]]
    h := ![![![548, -39, 0], ![4260, 1, 0]], ![![393, -28, 0], ![3055, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {640} * I109N2 =  Ideal.span {B.equivFun.symm ![92, -5, 2]} * (J0 ^ 11*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_1 E109RS2 


noncomputable def E113RS1 : RelationCertificate Table 800 ![![113, 0, 0], ![-46, 1, 0]]
  ![96, -30, 1] ![![800, 0, 0], ![125, 30, 1]] where
    su := ![![90400, 0, 0], ![-36800, 800, 0]]
    hsu := by decide
    w := ![![76800, -24000, 800], ![12000, -800, -1600]]
    hw := by decide
    g := ![![![-438572722, -332178830, -193297370], ![-81224849, 2578652013, 0]], ![![177965939, 134792980, 78437057], ![32959966, -1046376759, 0]]]
    h := ![![![4127992, -100618, 473], ![10140500, -26724, 0]], ![![644165, -15706, 74], ![1582405, -4182, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {800} * I113N1 =  Ideal.span {B.equivFun.symm ![96, -30, 1]} * (J0 ^ 6*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_2 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 320 ![![131, 0, 0], ![7, 1, 0]]
  ![-76, -5, -1] ![![320, 0, 0], ![-35, 62, 1]] where
    su := ![![41920, 0, 0], ![2240, 320, 0]]
    hsu := by decide
    w := ![![-24320, -1600, -320], ![-6720, -3200, -640]]
    hw := by decide
    g := ![![![-2, 0, 0], ![1, 0, 0]], ![![721, -318, 619], ![197, -1599, 0]]]
    h := ![![![-159660, -22882, -21], ![2987912, 1375, 0]], ![![-44135, -6326, -6], ![825952, 392, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {320} * I131N1 =  Ideal.span {B.equivFun.symm ![-76, -5, -1]} * (J0 ^ 10*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_1 E131RS1 


noncomputable def E137RS0 : RelationCertificate Table 12800 ![![137, 0, 0], ![31, 1, 0]]
  ![-372, 85, -7] ![![12800, 0, 0], ![-6115, 126, 1]] where
    su := ![![1753600, 0, 0], ![396800, 12800, 0]]
    hsu := by decide
    w := ![![-4761600, 1088000, -89600], ![2163200, -550400, 64000]]
    hw := by decide
    g := ![![![5803, -2480, 96], ![12037, -4926, 0]], ![![2711, -651, 24], ![5647, -1242, 0]]]
    h := ![![![-108538812, -3733146, -14961], ![479671512, 1024825, 0]], ![![49303808, 1695767, 6795], ![-217891017, -465455, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {12800} * I137N0 =  Ideal.span {B.equivFun.symm ![-372, 85, -7]} * (J0 ^ 14*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_14J1_2 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 1600 ![![137, 0, 0], ![48, 1, 0]]
  ![-1152, -90, -37] ![![1600, 0, 0], ![-355, 62, 1]] where
    su := ![![219200, 0, 0], ![76800, 1600, 0]]
    hsu := by decide
    w := ![![-1843200, -144000, -59200], ![75200, 8000, 1600]]
    hw := by decide
    g := ![![![266, -221, 61], ![887, -795, 0]], ![![537929, -1543969, 511569], ![-178132, -6599454, 0]]]
    h := ![![![-7392, -220, -3], ![21074, 187, 0]], ![![247, -19, -1], ![-704, 69, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {1600} * I137N1 =  Ideal.span {B.equivFun.symm ![-1152, -90, -37]} * (J0 ^ 8*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_2 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 1600 ![![137, 0, 0], ![58, 1, 0]]
  ![-716, -45, -21] ![![1600, 0, 0], ![-355, 62, 1]] where
    su := ![![219200, 0, 0], ![92800, 1600, 0]]
    hsu := by decide
    w := ![![-1145600, -72000, -33600], ![65600, -1600, 1600]]
    hw := by decide
    g := ![![![1476301893, -4238435270, 1404362204], ![-490915715, -18116843634, 0]], ![![631425196, -1812809321, 600655824], ![-209967066, -7748704446, 0]]]
    h := ![![![-6856, -143, -1], ![16182, 58, 0]], ![![361, -23, -1], ![-852, 69, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {1600} * I137N2 =  Ideal.span {B.equivFun.symm ![-716, -45, -21]} * (J0 ^ 8*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_2 E137RS2 
