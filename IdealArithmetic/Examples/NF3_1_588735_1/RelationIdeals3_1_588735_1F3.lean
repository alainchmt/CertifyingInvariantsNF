import IdealArithmetic.Examples.NF3_1_588735_1.PrimesBelow3_1_588735_1F3
import IdealArithmetic.Examples.NF3_1_588735_1.ClassGroupData3_1_588735_1

set_option linter.all false

noncomputable section


noncomputable def E149RS0 : RelationCertificate Table 275 ![![149, 0, 0], ![22, 1, 0]]
  ![-28772, -153, -945] ![![275, 0, 0], ![27, 1, 0]] where
    su := ![![40975, 0, 0], ![6050, 275, 0]]
    hsu := by decide
    w := ![![-7912300, -42075, -259875], ![-829125, -4400, -27225]]
    hw := by decide
    g := ![![![-30850371234008202, -406792523761787795, -78232484074681898], ![-4508191080290789, 4302786624068496375, 6965716]], ![![-7258910850660321, -95715887575667411, -18407643240863416], ![-1060750838339826, 1012420378238309523, 1638992]]]
    h := ![![![933449288, 10118798861, 2409566575], ![205736162, -71805084124, 0]], ![![97815579, 1060342833, 252497029], ![21559031, -7524411484, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N0 : Ideal.span {275} * I149N0 =  Ideal.span {B.equivFun.symm ![-28772, -153, -945]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E149RS0 


noncomputable def E149RS1 : RelationCertificate Table 5 ![![149, 0, 0], ![47, 1, 0]]
  ![-8, 3, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![745, 0, 0], ![235, 5, 0]]
    hsu := by decide
    w := ![![-40, 15, 0], ![-10, -5, 15]]
    hw := by decide
    g := ![![![3109, -2075, 189], ![832, 0, -318]], ![![1036, -692, 63], ![279, 0, -106]]]
    h := ![![![-677, -17708, -1925], ![-295, 57365, 0]], ![![-201, -4398, -478], ![31, 14245, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {5} * I149N1 =  Ideal.span {B.equivFun.symm ![-8, 3, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E149RS1 


noncomputable def E149RS2 : RelationCertificate Table 121 ![![149, 0, 0], ![-69, 1, 0]]
  ![14792, 79, 486] ![![121, 0, 0], ![-17, 1, 0]] where
    su := ![![18029, 0, 0], ![-8349, 121, 0]]
    hsu := by decide
    w := ![![1789832, 9559, 58806], ![-224576, -1210, -7381]]
    hw := by decide
    g := ![![![-460964423, 4274411925, -1187566419], ![100089390, 28739107348, 0]], ![![213126948, -1976274711, 549071433], ![-46276278, -13287528682, 0]]]
    h := ![![![706045, -33663570, 2404809], ![-552761, -71663211, 0]], ![![-88540, 4223874, -301739], ![69464, 8991810, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N2 : Ideal.span {121} * I149N2 =  Ideal.span {B.equivFun.symm ![14792, 79, 486]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E149RS2 


noncomputable def E151RS1 : RelationCertificate Table 25 ![![151, 0, 0], ![-39, 1, 0]]
  ![-597, -3, -20] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![3775, 0, 0], ![-975, 25, 0]]
    hsu := by decide
    w := ![![-14925, -75, -500], ![-2300, 0, -75]]
    hw := by decide
    g := ![![![-18732673128716, -9366305571118, -47206263539187], ![-1873266073138, 236031309610740, 13475322]], ![![4774995111533, 2387489655529, 12032969138180], ![477499195167, -60164843629968, -3434886]]]
    h := ![![![-3201732, 70717540, -8840765], ![1295417, 266991099, 0]], ![![-493391, 10898301, -1362453], ![199749, 41146080, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {25} * I151N1 =  Ideal.span {B.equivFun.symm ![-597, -3, -20]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 605 ![![157, 0, 0], ![-7, 1, 0]]
  ![-117749, -631, -3865] ![![605, 0, 0], ![-138, 1, 0]] where
    su := ![![94985, 0, 0], ![-4235, 605, 0]]
    hsu := by decide
    w := ![![-71238145, -381755, -2338325], ![16035525, 85910, 526350]]
    hw := by decide
    g := ![![![186449205, -13999124460, 503569390], ![-65667332, -60931913287, -625]], ![![-7457875, 559965239, -20142785], ![2627118, 2437277669, 25]]]
    h := ![![![-15895616235, 63774200967, -39863314035], ![1114926958, 1251708059926, 0]], ![![3578062781, -14355410386, 8973130570], ![-250967048, -281756299724, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {605} * I157N1 =  Ideal.span {B.equivFun.symm ![-117749, -631, -3865]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E157RS1 


noncomputable def E179RS1 : RelationCertificate Table 605 ![![179, 0, 0], ![30, 1, 0]]
  ![963, 7, 40] ![![605, 0, 0], ![-138, 1, 0]] where
    su := ![![108295, 0, 0], ![18150, 605, 0]]
    hsu := by decide
    w := ![![582615, 4235, 24200], ![-130680, -1210, -5445]]
    hw := by decide
    g := ![![![-38327602327, 2877421665595, -103493686064], ![13498563891, 12524115795246, 50356989]], ![![-7006120878, 525980304398, -18918200676], ![2467479318, 2289354499920, 9205041]]]
    h := ![![![6698609, 101223129, 17453890], ![1688282, -624849254, 0]], ![![-1502002, -22696713, -3913591], ![-378499, 140106556, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {605} * I179N1 =  Ideal.span {B.equivFun.symm ![963, 7, 40]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E179RS1 


noncomputable def E181RS1 : RelationCertificate Table 3025 ![![181, 0, 0], ![-88, 1, 0]]
  ![19597, 128, 645] ![![3025, 0, 0], ![-1348, 1, 0]] where
    su := ![![547525, 0, 0], ![-266200, 3025, 0]]
    hsu := by decide
    w := ![![59280925, 387200, 1951125], ![-26381025, -172425, -868175]]
    hw := by decide
    g := ![![![-58539984, 52547425260, -194764235], ![43458097, 117832472096, 408]], ![![28123349, -25243375025, 93563226], ![-20874250, -56605804536, -196]]]
    h := ![![![1327935, -82965333, 4661320], ![-1103894, -168739655, 0]], ![![-590869, 36920989, -2074367], ![491426, 75092028, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {3025} * I181N1 =  Ideal.span {B.equivFun.symm ![19597, 128, 645]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E181RS1 
