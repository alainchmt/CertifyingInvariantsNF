import IdealArithmetic.Examples.NF3_1_780332_1.PrimesBelow3_1_780332_1F1
import IdealArithmetic.Examples.NF3_1_780332_1.ClassGroupData3_1_780332_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 19683 ![![37, 0, 0], ![-16, 1, 0]]
  ![-585, 41, -1] ![![19683, 0, 0], ![-504, 5, 1]] where
    su := ![![728271, 0, 0], ![-314928, 19683, 0]]
    hsu := by decide
    w := ![![-11514555, 807003, -19683], ![314928, -19683, 0]]
    hw := by decide
    g := ![![![19046918153, -12979456607, 170808910], ![-490994384, -672308156230, 0]], ![![-7309925328, 4981323435, -65553933], ![188439938, 258021924660, 0]]]
    h := ![![![-2821, 208, -2], ![-6487, 73, 0]], ![![80, -5, 0], ![184, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {19683} * I37N1 =  Ideal.span {B.equivFun.symm ![-585, 41, -1]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 177147 ![![43, 0, 0], ![-3, 1, 0]]
  ![8919, 830, -121] ![![177147, 0, 0], ![-13545, 167, 1]] where
    su := ![![7617321, 0, 0], ![-531441, 177147, 0]]
    hsu := by decide
    w := ![![1579974093, 147032010, -21434787], ![-131620221, -12223143, 1771470]]
    hw := by decide
    g := ![![![163807174100, -3969786110081, 49397069800], ![-16267001495, -52398362017120, 0]], ![![-10815155820, 262100121434, -3261379238], ![1074090237, 3459535771160, 0]]]
    h := ![![![4952665884, -1658537672, 2549708], ![70988208031, -109637565, 0]], ![![-412583576, 138165067, -212405], ![-5913697675, 9133425, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {177147} * I43N1 =  Ideal.span {B.equivFun.symm ![8919, 830, -121]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E43RS1 


noncomputable def E53RS0 : RelationCertificate Table 59049 ![![53, 0, 0], ![2, 1, 0]]
  ![-93375, -27995, -2168] ![![59049, 0, 0], ![-504, 5, 1]] where
    su := ![![3129597, 0, 0], ![118098, 59049, 0]]
    hsu := by decide
    w := ![![-5513700375, -1653076755, -128018232], ![25391070, 7617321, 590490]]
    hw := by decide
    g := ![![![16675, -11022, 144], ![58703, -1711928, 0]], ![![988, -498, 6], ![30491, -76986, 0]]]
    h := ![![![-10608787481, -5312230850, -3918772], ![281132821559, 207692748, 0]], ![![48854402, 24463291, 18046], ![-1294641438, -956428, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {59049} * I53N0 =  Ideal.span {B.equivFun.symm ![-93375, -27995, -2168]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 531441 ![![53, 0, 0], ![10, 1, 0]]
  ![430821, 129065, 9980] ![![531441, 0, 0], ![163602, 167, 1]] where
    su := ![![28166373, 0, 0], ![5314410, 531441, 0]]
    hsu := by decide
    w := ![![228955943061, 68590432665, 5303781180], ![71485191792, 21415477977, 1655970156]]
    hw := by decide
    g := ![![![5984783593227, 1978608419776959, 2018170457117], ![2464153601198, -6422401138049780, 0]], ![![1168485021154, 386308776069184, 394032973576], ![481108113175, -1253926698313268, 0]]]
    h := ![![![1167797, 122779, 626], ![-6146242, -23198, 0]], ![![364604, 38329, 195], ![-1918950, -7219, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {531441} * I53N1 =  Ideal.span {B.equivFun.symm ![430821, 129065, 9980]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 6561 ![![53, 0, 0], ![-12, 1, 0]]
  ![801, 88, -14] ![![6561, 0, 0], ![34461, 104, -422]] where
    su := ![![347733, 0, 0], ![-78732, 6561, 0]]
    hsu := by decide
    w := ![![5255361, 577368, -91854], ![6068925, 1627128, -78732]]
    hw := by decide
    g := ![![![105847063448, 221275951312, 34501938556], ![557239619777, 84499045000, 0]], ![![529229828, 1106379740, 172509760], ![2786199144, 422495225, 0]]]
    h := ![![![74275521, -6445791, 21347], ![328050151, -1131405, 0]], ![![85680245, -7435829, 24651], ![378421005, -1306515, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {6561} * I53N2 =  Ideal.span {B.equivFun.symm ![801, 88, -14]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E53RS2 


noncomputable def E59RS1 : RelationCertificate Table 27 ![![59, 0, 0], ![17, 1, 0]]
  ![-513, -25, 5] ![![27, 0, 0], ![654, 35, -8]] where
    su := ![![1593, 0, 0], ![459, 27, 0]]
    hsu := by decide
    w := ![![-13851, -675, 135], ![-126252, -10125, 1539]]
    hw := by decide
    g := ![![![-259, -6228, -1226], ![-11539, -1692, 0]], ![![-297, -1809, -351], ![-3319, -488, 0]]]
    h := ![![![-980, -76, -1], ![3371, 64, 0]], ![![-8940, -578, -2], ![30752, 175, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {27} * I59N1 =  Ideal.span {B.equivFun.symm ![-513, -25, 5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS1 


noncomputable def E71RS0 : RelationCertificate Table 531441 ![![71, 0, 0], ![3, 1, 0]]
  ![-102663, 6337, 124] ![![531441, 0, 0], ![163602, 167, 1]] where
    su := ![![37732311, 0, 0], ![1594323, 531441, 0]]
    hsu := by decide
    w := ![![-54559327383, 3367741617, 65898684], ![-16780781016, 1023023925, 21257640]]
    hw := by decide
    g := ![![![10596730238791, 3503348015507521, 3573397037648], ![4363060275736, -11371581186496945, 0]], ![![507909086575, 167918068854957, 171275570442], ![209124888873, -545048320695575, 0]]]
    h := ![![![-102579, -33684, -19], ![2393482, 1473, 0]], ![![-31550, -10361, -6], ![736158, 466, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {531441} * I71N0 =  Ideal.span {B.equivFun.symm ![-102663, 6337, 124]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 81 ![![71, 0, 0], ![26, 1, 0]]
  ![117, 14, -1] ![![81, 0, 0], ![-1833, -172, 22]] where
    su := ![![5751, 0, 0], ![2106, 81, 0]]
    hsu := by decide
    w := ![![9477, 1134, -81], ![53379, 1458, -729]]
    hw := by decide
    g := ![![![-34251138, 182955594, 18281013], ![391572607, 58693950, 0]], ![![-13229245, 70665391, 7060920], ![151242331, 22670150, 0]]]
    h := ![![![153985, 7015, 42], ![-420493, -2983, 0]], ![![866159, 39583, 241], ![-2365255, -17120, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {81} * I71N1 =  Ideal.span {B.equivFun.symm ![117, 14, -1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 9 ![![71, 0, 0], ![-29, 1, 0]]
  ![-567, -169, -13] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![639, 0, 0], ![-261, 9, 0]]
    hsu := by decide
    w := ![![-5103, -1521, -117], ![-4986, -1503, -117]]
    hw := by decide
    g := ![![![209, 127, -28], ![-70, 226, 0]], ![![-103, -52, 11], ![40, -86, 0]]]
    h := ![![![-173448, 6698, -25], ![-424629, 1762, 0]], ![![-169474, 6532, -24], ![-414900, 1691, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {9} * I71N2 =  Ideal.span {B.equivFun.symm ![-567, -169, -13]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E71RS2 


noncomputable def E79RS1 : RelationCertificate Table 177147 ![![79, 0, 0], ![38, 1, 0]]
  ![4905, 919, 25] ![![177147, 0, 0], ![-13545, 167, 1]] where
    su := ![![13994613, 0, 0], ![6731586, 177147, 0]]
    hsu := by decide
    w := ![![868906035, 162798093, 4428675], ![-63595773, -10983114, -177147]]
    hw := by decide
    g := ![![![-440354983662, 10671786659992, -132791786747], ![43730192311, 140860017465146, 0]], ![![-232791412435, 5641585487894, -70199699534], ![23117737277, 74464928476722, 0]]]
    h := ![![![16102099595, 586984041, 4295910], ![-33475417450, -339376865, 0]], ![![-1178172437, -42952536, -314421], ![2449358478, 24839258, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {177147} * I79N1 =  Ideal.span {B.equivFun.symm ![4905, 919, 25]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E79RS1 
