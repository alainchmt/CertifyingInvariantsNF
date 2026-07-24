import IdealArithmetic.Examples.NF3_1_536787_1.PrimesBelow3_1_536787_1F2
import IdealArithmetic.Examples.NF3_1_536787_1.ClassGroupData3_1_536787_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 8 ![![83, 0, 0], ![30, 1, 0]]
  ![95, -13, -1] ![![8, 0, 0], ![3, 1, 0]] where
    su := ![![664, 0, 0], ![240, 8, 0]]
    hsu := by decide
    w := ![![760, -104, -8], ![144, 56, -16]]
    hw := by decide
    g := ![![![49573, -1203898, -406798], ![-131895, 3254417, 0]], ![![17958, -435995, -147323], ![-47761, 1178598, 0]]]
    h := ![![![865, 29, 0], ![-2390, -1, 0]], ![![126, 5, 0], ![-348, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {8} * I83N1 =  Ideal.span {B.equivFun.symm ![95, -13, -1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 40 ![![89, 0, 0], ![12, 1, 0]]
  ![-73, 19, -1] ![![40, 0, 0], ![-14, 1, 1]] where
    su := ![![3560, 0, 0], ![480, 40, 0]]
    hsu := by decide
    w := ![![-2920, 760, -40], ![3560, -480, -40]]
    hw := by decide
    g := ![![![4915159, -504916, 82426], ![-1730841, -1566235, 0]], ![![1251136, -128524, 20981], ![-440569, -398678, 0]]]
    h := ![![![-29285, -2500, -5], ![217191, 444, 0]], ![![35701, 3035, 5], ![-264775, -446, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {40} * I89N1 =  Ideal.span {B.equivFun.symm ![-73, 19, -1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 8 ![![101, 0, 0], ![-7, 1, 0]]
  ![17, 5, 1] ![![8, 0, 0], ![3, 1, 0]] where
    su := ![![808, 0, 0], ![-56, 8, 0]]
    hsu := by decide
    w := ![![136, 40, 8], ![192, 32, 8]]
    hw := by decide
    g := ![![![-43442714, 1057105880, 357195594], ![115847220, -2857564751, 0]], ![![3440869, -83727847, -28291601], ![-9175649, 226332808, 0]]]
    h := ![![![50, -7, 0], ![719, 1, 0]], ![![64, -9, 0], ![920, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {8} * I101N1 =  Ideal.span {B.equivFun.symm ![17, 5, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 8 ![![107, 0, 0], ![46, 1, 0]]
  ![-7, -3, 1] ![![8, 0, 0], ![3, 1, 0]] where
    su := ![![856, 0, 0], ![368, 8, 0]]
    hsu := by decide
    w := ![![-56, -24, 8], ![120, -16, 0]]
    hw := by decide
    g := ![![![1, 65, 22], ![17, -174, 0]], ![![-1, 32, 11], ![12, -87, 0]]]
    h := ![![![-71, -2, 0], ![165, 1, 0]], ![![-45, -1, 0], ![105, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {8} * I107N1 =  Ideal.span {B.equivFun.symm ![-7, -3, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 2 ![![109, 0, 0], ![30, 1, 0]]
  ![-131, -157, 35] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![218, 0, 0], ![60, 2, 0]]
    hsu := by decide
    w := ![![-262, -314, 70], ![4804, -288, -122]]
    hw := by decide
    g := ![![![158678, -1435, 7145], ![78622, 327, 0]], ![![51248, -456, 2317], ![25397, 87, 0]]]
    h := ![![![-1199, -51, 0], ![4352, 35, 0]], ![![21458, 760, 1], ![-77884, -170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {2} * I109N0 =  Ideal.span {B.equivFun.symm ![-131, -157, 35]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 40 ![![109, 0, 0], ![37, 1, 0]]
  ![-1481, -85, 71] ![![40, 0, 0], ![-14, 1, 1]] where
    su := ![![4360, 0, 0], ![1480, 40, 0]]
    hsu := by decide
    w := ![![-59240, -3400, 2840], ![18760, 9720, -2560]]
    hw := by decide
    g := ![![![-1330952996, 136719182, -22320429], ![468693546, 424109567, 0]], ![![-439581296, 45154852, -7371910], ![154798071, 140072890, 0]]]
    h := ![![![-1488824, -46294, -163], ![4385955, 17838, 0]], ![![473162, 14699, 51], ![-1393897, -5623, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {40} * I109N1 =  Ideal.span {B.equivFun.symm ![-1481, -85, 71]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E109RS1 


noncomputable def E109RS2 : RelationCertificate Table 5 ![![109, 0, 0], ![42, 1, 0]]
  ![53, 10, 2] ![![5, 0, 0], ![1, 1, 1]] where
    su := ![![545, 0, 0], ![210, 5, 0]]
    hsu := by decide
    w := ![![265, 50, 10], ![1745, 345, 65]]
    hw := by decide
    g := ![![![-3, 6, -2], ![4, 0, 0]], ![![-3, 2, -1], ![3, 0, 0]]]
    h := ![![![239, 5, 0], ![-619, 2, 0]], ![![1531, 32, 0], ![-3965, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N2 : Ideal.span {5} * I109N2 =  Ideal.span {B.equivFun.symm ![53, 10, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E109RS2 


noncomputable def E113RS1 : RelationCertificate Table 8 ![![113, 0, 0], ![-16, 1, 0]]
  ![4253, 817, 157] ![![8, 0, 0], ![3, 1, 0]] where
    su := ![![904, 0, 0], ![-128, 8, 0]]
    hsu := by decide
    w := ![![34024, 6536, 1256], ![34896, 6704, 1288]]
    hw := by decide
    g := ![![![-387877469, 9438352427, 3189214968], ![1034340004, -25513719773, 0]], ![![58353064, -1419924772, -479791931], ![-155608195, 3838335453, 0]]]
    h := ![![![549245, -34968, 42], ![3878777, -4589, 0]], ![![563338, -35864, 43], ![3978302, -4698, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {8} * I113N1 =  Ideal.span {B.equivFun.symm ![4253, 817, 157]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 10 ![![131, 0, 0], ![43, 1, 0]]
  ![-13, -3, 1] ![![10, 0, 0], ![-4, 1, 1]] where
    su := ![![1310, 0, 0], ![430, 10, 0]]
    hsu := by decide
    w := ![![-130, -30, 10], ![-230, 140, -20]]
    hw := by decide
    g := ![![![-3061858, -20248, -145956], ![1208125, 251424, 0]], ![![-1052512, -6961, -50173], ![415299, 86427, 0]]]
    h := ![![![-243, -49, -1], ![740, 132, 0]], ![![-377, -51, -1], ![1148, 129, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {10} * I131N1 =  Ideal.span {B.equivFun.symm ![-13, -3, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E131RS1 


noncomputable def E137RS1 : RelationCertificate Table 20 ![![137, 0, 0], ![-14, 1, 0]]
  ![-203, 13, 5] ![![20, 0, 0], ![6, 1, 1]] where
    su := ![![2740, 0, 0], ![-280, 20, 0]]
    hsu := by decide
    w := ![![-4060, 260, 100], ![1320, 580, -160]]
    hw := by decide
    g := ![![![-24020566, -752704, 176009], ![-7234985, 3715101, 0]], ![![2267434, 71053, -16615], ![682969, -350688, 0]]]
    h := ![![![-1141, 96, -1], ![-11151, 142, 0]], ![![398, -15, -1], ![3890, 129, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {20} * I137N1 =  Ideal.span {B.equivFun.symm ![-203, 13, 5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E137RS1 
