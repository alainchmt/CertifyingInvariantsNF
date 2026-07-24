import IdealArithmetic.Examples.NF3_1_387731_1.PrimesBelow3_1_387731_1F0
import IdealArithmetic.Examples.NF3_1_387731_1.ClassGroupData3_1_387731_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![29, 0, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![58, 0, 2], ![4, 0, 0]]
    hw := by decide
    g := ![![![14, -102, 0], ![2, 0, -7]], ![![14, -102, 1], ![2, 0, -7]]]
    h := ![![![367, -1083, 44], ![-357, 0, -87]], ![![25, -75, 3], ![-24, 0, -6]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![29, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 10 ![![5, 0, 0], ![2, 1, 0]]
  ![17, -88, 163] ![![10, 0, 0], ![34, 1, 2]] where
    su := ![![50, 0, 0], ![20, 10, 0]]
    hsu := by decide
    w := ![![170, -880, 1630], ![200, -2360, -4230]]
    hw := by decide
    g := ![![![191649, -60834, -45976], ![636405, 0, 0]], ![![81935, -26014, -19661], ![272141, 0, 0]]]
    h := ![![![-7, 144, 255], ![26, -278, 0]], ![![-18, 297, 389], ![55, -592, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {10} * I5N0 =  Ideal.span {B.equivFun.symm ![17, -88, 163]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, -7, 1] ![![5, 0, 0], ![17, -2, 1]] where
    su := ![![25, 0, 0], ![-10, 5, 0]]
    hsu := by decide
    w := ![![5, -35, 5], ![-20, 155, 45]]
    hw := by decide
    g := ![![![111, 146, -26], ![361, 0, 0]], ![![-53, -53, 9], ![-131, 0, 0]]]
    h := ![![![1, 0, -7], ![2, 9, 0]], ![![0, -2, 33], ![2, -39, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![1, -7, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 2 ![![5, 0, 0], ![-1, 1, 0]]
  ![-68237275, -81305, -2355426] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![10, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![-136474550, -162610, -4710852], ![-9421704, -11226, -325220]]
    hw := by decide
    g := ![![![-163, 959, 88], ![481, 0, 0]], ![![103, -435, 942], ![-216, 0, 0]]]
    h := ![![![-13142595, -521121, 16487982], ![2524300, -21198834, 0]], ![![-907316, -35977, 1138270], ![174272, -1463490, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {2} * I5N2 =  Ideal.span {B.equivFun.symm ![-68237275, -81305, -2355426]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![20, -1, 1]]
  ![-15937837, -18990, -550145] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![40, -2, 2]]
    hsu := by decide
    w := ![![-31875674, -37980, -1100290], ![-2200580, -2622, -75960]]
    hw := by decide
    g := ![![![-36, 206, -15], ![103, 0, 0]], ![![55, -342, -133], ![-170, 0, 0]]]
    h := ![![![-254111, -103849, 22544], ![-707953, 0, 0]], ![![-17550, -7169, 1556], ![-48872, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-15937837, -18990, -550145]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![-3, 1, 0]]
  ![-1, 15, 36] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![-2, 30, 72], ![144, -1030, 60]]
    hw := by decide
    g := ![![![550145, 524, 18990], ![263, 0, 0]], ![![-224925, -214, -7764], ![-108, 0, 0]]]
    h := ![![![-7, 5, 4], ![-16, 2, 0]], ![![582, -265, 6], ![1334, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![-1, 15, 36]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 10 ![![11, 0, 0], ![24, -5, 1]]
  ![1, -8, -5] ![![10, 0, 0], ![34, 1, 2]] where
    su := ![![110, 0, 0], ![240, -50, 10]]
    hsu := by decide
    w := ![![10, -80, -50], ![-40, 320, 90]]
    hw := by decide
    g := ![![![1, -7, -6], ![73, 0, 0]], ![![31, -14, -11], ![146, 0, 0]]]
    h := ![![![11, -3, 0], ![-5, 0, 0]], ![![-20, 7, 0], ![9, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {10} * I11N0 =  Ideal.span {B.equivFun.symm ![1, -8, -5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 10 ![![11, 0, 0], ![-2, 1, 0]]
  ![27, 0, 1] ![![10, 0, 0], ![34, 1, 2]] where
    su := ![![110, 0, 0], ![-20, 10, 0]]
    hsu := by decide
    w := ![![270, 0, 10], ![920, 0, 30]]
    hw := by decide
    g := ![![![-3, 0, 0], ![1, 0, 0]], ![![17, 0, 1], ![-5, 0, 0]]]
    h := ![![![3, 12, -49], ![3, 135, 0]], ![![10, 41, -167], ![9, 460, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {10} * I11N1 =  Ideal.span {B.equivFun.symm ![27, 0, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 5 ![![13, 0, 0], ![24, 6, 1]]
  ![175, -1058, 972] ![![5, 0, 0], ![17, -2, 1]] where
    su := ![![65, 0, 0], ![120, 30, 5]]
    hsu := by decide
    w := ![![875, -5290, 4860], ![-10005, 71810, -3025]]
    hw := by decide
    g := ![![![1347064, 1575332, -275367], ![3894871, 0, 0]], ![![2569675, 3005086, -525286], ![7429813, 0, 0]]]
    h := ![![![-5, -86, 74], ![10, 0, 0]], ![![-261, 1078, -51], ![58, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {5} * I13N0 =  Ideal.span {B.equivFun.symm ![175, -1058, 972]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 5 ![![13, 0, 0], ![2, 1, 0]]
  ![-54551, -65, -1883] ![![5, 0, 0], ![17, -2, 1]] where
    su := ![![65, 0, 0], ![10, 5, 0]]
    hsu := by decide
    w := ![![-272755, -325, -9415], ![-910680, -1085, -31435]]
    hw := by decide
    g := ![![![-10, 26, 9], ![2, 0, 0]], ![![-18, -13, 8], ![6, 0, 0]]]
    h := ![![![-375609, -197188, -15447], ![2414183, 49732, 0]], ![![-1254088, -658374, -51575], ![8060504, 166047, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {5} * I13N1 =  Ideal.span {B.equivFun.symm ![-54551, -65, -1883]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 10 ![![17, 0, 0], ![-8, 1, 0]]
  ![2905571, 3462, 100295] ![![10, 0, 0], ![34, 1, 2]] where
    su := ![![170, 0, 0], ![-80, 10, 0]]
    hsu := by decide
    w := ![![29055710, 34620, 1002950], ![99017700, 117980, 3417910]]
    hw := by decide
    g := ![![![-11, 22, 76], ![3, 0, 0]], ![![-19, -141, -33], ![11, 0, 0]]]
    h := ![![![410235, 11927277, -6826665], ![508553, 29038400, 0]], ![![1398026, 40646452, -23264297], ![1733084, 98958710, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {10} * I17N1 =  Ideal.span {B.equivFun.symm ![2905571, 3462, 100295]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 5 ![![19, 0, 0], ![8, 1, 0]]
  ![59, 0, 2] ![![5, 0, 0], ![17, -2, 1]] where
    su := ![![95, 0, 0], ![40, 5, 0]]
    hsu := by decide
    w := ![![295, 0, 10], ![985, 0, 35]]
    hw := by decide
    g := ![![![-10, 2, -1], ![3, 0, 0]], ![![0, 1, 0], ![0, 0, 0]]]
    h := ![![![1001, 165, 18], ![-2370, -85, 0]], ![![3383, 576, 69], ![-8010, -326, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {5} * I19N1 =  Ideal.span {B.equivFun.symm ![59, 0, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E19RS1 
