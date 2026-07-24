import IdealArithmetic.Examples.NF3_1_567567_2.PrimesBelow3_1_567567_2F1
import IdealArithmetic.Examples.NF3_1_567567_2.ClassGroupData3_1_567567_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 100 ![![37, 0, 0], ![17, 1, 0]]
  ![-401839, 109309, 13793] ![![100, 0, 0], ![12, 1, 1]] where
    su := ![![3700, 0, 0], ![1700, 100, 0]]
    hsu := by decide
    w := ![![-40183900, 10930900, 1379300], ![6947100, -1863200, -294600]]
    hw := by decide
    g := ![![![-1170348148, 134117264, -33919718], ![-139439763, 992278314, 0]], ![![-574294251, 64022676, -16690609], ![-68441915, 476900353, 0]]]
    h := ![![![1424778584, 17449846180, 3884507549], ![1126245489, -35931691380, 0]], ![![-246280742, -3016300785, -671458266], ![-194677619, 6210988224, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {100} * I37N1 =  Ideal.span {B.equivFun.symm ![-401839, 109309, 13793]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 20 ![![43, 0, 0], ![-8, 1, 0]]
  ![-84247, -3163, -2831] ![![20, 0, 0], ![12, 1, 1]] where
    su := ![![860, 0, 0], ![-160, 20, 0]]
    hsu := by decide
    w := ![![-1684940, -63260, -56620], ![-1441500, -54120, -48440]]
    hw := by decide
    g := ![![![-1928, 413, -17], ![-1123, 500, 0]], ![![314, -69, 3], ![188, -81, 0]]]
    h := ![![![50549121, -185543367, 106206991], ![-13719409, -1141725861, 0]], ![![43245787, -158736077, 90862214], ![-11737237, -976769406, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {20} * I43N1 =  Ideal.span {B.equivFun.symm ![-84247, -3163, -2831]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![-2, 1, 0]]
  ![73, -13, -17] ![![2, 0, 0], ![18, 1, 1]] where
    su := ![![94, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![146, -26, -34], ![-654, 92, 204]]
    hw := by decide
    g := ![![![-922, 698, 1366], ![-7155, -72, 0]], ![![-44, 57, 49], ![-252, 3, 0]]]
    h := ![![![11, -5, 17], ![18, -204, 0]], ![![-57, 26, -102], ![48, 1224, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![73, -13, -17]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS1 


noncomputable def E53RS0 : RelationCertificate Table 10 ![![53, 0, 0], ![7, 1, 0]]
  ![343581, -156841, 122163] ![![10, 0, 0], ![22, 1, 1]] where
    su := ![![530, 0, 0], ![70, 10, 0]]
    hsu := by decide
    w := ![![3435810, -1568410, 1221630], ![-4075810, 1581760, -859920]]
    hw := by decide
    g := ![![![-22846523237783, 10012958992153, 1100847809276], ![-49150970442931, 12730753663622, 0]], ![![-2907917514557, 1275234098643, 140160117564], ![-6255879110353, 1621369570317, 0]]]
    h := ![![![3402581, 13944417, 6982715], ![712522, -92490433, 0]], ![![-4029233, -16512988, -8267568], ![-843684, 109523778, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {10} * I53N0 =  Ideal.span {B.equivFun.symm ![343581, -156841, 122163]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 10 ![![53, 0, 0], ![21, 1, 0]]
  ![-7113, -267, -239] ![![10, 0, 0], ![22, 1, 1]] where
    su := ![![530, 0, 0], ![210, 10, 0]]
    hsu := by decide
    w := ![![-71130, -2670, -2390], ![-192830, -7240, -6480]]
    hw := by decide
    g := ![![![-544, 236, 28], ![-1159, 300, 0]], ![![-273, 114, 13], ![-563, 147, 0]]]
    h := ![![![-51195, -707433, -128743], ![-33588, 1705785, 0]], ![![-138758, -1917815, -349016], ![-91129, 4624300, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {10} * I53N1 =  Ideal.span {B.equivFun.symm ![-7113, -267, -239]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 10 ![![53, 0, 0], ![25, 1, 0]]
  ![-865581782409, -32497672431, -29086774547] ![![10, 0, 0], ![22, 1, 1]] where
    su := ![![530, 0, 0], ![250, 10, 0]]
    hsu := by decide
    w := ![![-8655817824090, -324976724310, -290867745470], ![-23466270131630, -881024965420, -788554152420]]
    hw := by decide
    g := ![![![-370892580000220325697, 162371191225400378238, 17861183326378410107], ![-797940438545306837693, 206442868427174314926, 0]], ![![-173199836886895337411, 75824282694880355632, 8340835609959725325], ![-372623129320685734177, 96404924407029517137, 0]]]
    h := ![![![8003066957282, 143930584267436, 22161553273721], ![6490702984901, -293647852570440, 0]], ![![21696636287599, 390201600734136, 60080861938926], ![17596556753330, -796091134544580, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {10} * I53N2 =  Ideal.span {B.equivFun.symm ![-865581782409, -32497672431, -29086774547]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS2 


noncomputable def E59RS1 : RelationCertificate Table 4 ![![59, 0, 0], ![-18, 1, 0]]
  ![-501, 143, 3] ![![4, 0, 0], ![20, 1, 1]] where
    su := ![![236, 0, 0], ![-72, 4, 0]]
    hsu := by decide
    w := ![![-2004, 572, 12], ![4820, -1344, -96]]
    hw := by decide
    g := ![![![6149, -1753, -2242], ![29795, -52, 0]], ![![-1520, 432, 552], ![-7338, 13, 0]]]
    h := ![![![-126129, 1224694, -288399], ![59259, 4253886, 0]], ![![303325, -2945087, 693528], ![-142451, -10229544, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {4} * I59N1 =  Ideal.span {B.equivFun.symm ![-501, 143, 3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![-5, 1, 0]]
  ![-30865659383329, -1158829943503, -1037201214227] ![![2, 0, 0], ![18, 1, 1]] where
    su := ![![122, 0, 0], ![-10, 2, 0]]
    hsu := by decide
    w := ![![-61731318766658, -2317659887006, -2074402428454], ![-713317798007130, -26781025906440, -23970137071568]]
    hw := by decide
    g := ![![![-209779, 2290429, 43052], ![-721107, 13122, 0]], ![![-1504, -98581, 147869], ![11251, -729, 0]]]
    h := ![![![287324387391971, -580558725074083, 581064831701713], ![-33068535443160, -8861497983754680, 0]], ![![3320091056257910, -6708472776177679, 6714320940001016], ![-382113574712561, -102396390602149440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![-30865659383329, -1158829943503, -1037201214227]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 4 ![![67, 0, 0], ![24, 1, 0]]
  ![33413, -41671, 67717] ![![4, 0, 0], ![20, 1, 1]] where
    su := ![![268, 0, 0], ![96, 4, 0]]
    hsu := by decide
    w := ![![133652, -166684, 270868], ![-1118324, 622024, -633336]]
    hw := by decide
    g := ![![![-9894198407, 2613117557, 3595973226], ![-47918719273, 115668, 0]], ![![-4056476832, 1071326301, 1474296131], ![-19645978452, 41769, 0]]]
    h := ![![![-3093733, -46736894, -7481105], ![-1805723, 125325438, 0]], ![![24713233, 373343532, 59766678], ![14424862, -1001131440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {4} * I67N1 =  Ideal.span {B.equivFun.symm ![33413, -41671, 67717]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E67RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![-21, 1, 0]]
  ![-495839, 132419, 22219] ![![2, 0, 0], ![18, 1, 1]] where
    su := ![![158, 0, 0], ![-42, 2, 0]]
    hsu := by decide
    w := ![![-991678, 264838, 44438], ![5536158, -1444096, -320772]]
    hw := by decide
    g := ![![![9426658435, -11348422398, -13946073329], ![72192678143, 30240, 0]], ![![-2091873894, 2518326940, 3094779538], ![-16020311689, -7875, 0]]]
    h := ![![![22135230, -245191014, 49061573], ![-8987715, -968960512, 0]], ![![-123522173, 1368250630, -273780958], ![50154662, 5407133824, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![-495839, 132419, 22219]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS1 
