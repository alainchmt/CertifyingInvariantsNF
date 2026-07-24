import IdealArithmetic.Examples.NF3_1_996008_1.PrimesBelow3_1_996008_1F1
import IdealArithmetic.Examples.NF3_1_996008_1.ClassGroupData3_1_996008_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 3 ![![37, 0, 0], ![-1, 1, 0]]
  ![-94473331, -24984122, -3452662] ![![3, 0, 0], ![-18, -1, 1]] where
    su := ![![111, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![-283419993, -74952366, -10357986], ![-2562709122, -677726049, -93657843]]
    hw := by decide
    g := ![![![1223, -9783, 1919], ![-3419, 0, 0]], ![![43, 1151, -58], ![-590, 0, 0]]]
    h := ![![![-5237032, 2010740, -95603], ![-99296853, 84649, 0]], ![![-47353730, 18181299, -864443], ![-897851636, 765110, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {3} * I37N1 =  Ideal.span {B.equivFun.symm ![-94473331, -24984122, -3452662]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E37RS1 


noncomputable def E41RS0 : RelationCertificate Table 27 ![![41, 0, 0], ![15, 1, 0]]
  ![180729, 47795, 6605] ![![27, 0, 0], ![-13, 1, 0]] where
    su := ![![1107, 0, 0], ![405, 27, 0]]
    hsu := by decide
    w := ![![4879683, 1290465, 178335], ![-1041687, -275481, -38070]]
    hw := by decide
    g := ![![![201, 4561, -355], ![88, 9450, 0]], ![![57, 1675, -130], ![48, 3470, 0]]]
    h := ![![![607824, 46972, 533], ![-1649337, -15248, 0]], ![![-129776, -10032, -114], ![352149, 3264, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {27} * I41N0 =  Ideal.span {B.equivFun.symm ![180729, 47795, 6605]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 27 ![![41, 0, 0], ![-12, 1, 0]]
  ![-85059, -99907, 15431] ![![27, 0, 0], ![-13, 1, 0]] where
    su := ![![1107, 0, 0], ![-324, 27, 0]]
    hsu := by decide
    w := ![![-2296593, -2697489, 416637], ![4161105, 1599507, -300510]]
    hw := by decide
    g := ![![![163553108, 55856876, 7326515], ![-76679015, 1134, 0]], ![![-19003301, -6490078, -851268], ![8909391, -217, 0]]]
    h := ![![![-32781963, 2907749, -14501], ![-111997952, 609972, 0]], ![![59906947, -5313701, 26663], ![204669226, -1104313, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {27} * I41N1 =  Ideal.span {B.equivFun.symm ![-85059, -99907, 15431]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 9 ![![41, 0, 0], ![-3, 1, 0]]
  ![-192524769, -50914499, -7036091] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![369, 0, 0], ![-27, 9, 0]]
    hsu := by decide
    w := ![![-1732722921, -458230491, -63324819], ![-623046942, -164769048, -22770135]]
    hw := by decide
    g := ![![![2607, -2317, 267], ![-1414, 264, 0]], ![![1021, 489, -84], ![-390, -8, 0]]]
    h := ![![![-220579557, 71075656, -290344], ![-2950412356, 4868013, 0]], ![![-79315288, 25557156, -104401], ![-1060899790, 1750426, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {9} * I41N2 =  Ideal.span {B.equivFun.symm ![-192524769, -50914499, -7036091]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E41RS2 


noncomputable def E53RS1 : RelationCertificate Table 2187 ![![53, 0, 0], ![-16, 1, 0]]
  ![639, -67, -1] ![![2187, 0, 0], ![681, -1, 1]] where
    su := ![![115911, 0, 0], ![-34992, 2187, 0]]
    hsu := by decide
    w := ![![1397493, -146529, -2187], ![422091, -48114, 0]]
    hw := by decide
    g := ![![![17539, 70977, -104], ![7598, -219857, 0]], ![![-6123, -21327, 30], ![455, 66066, 0]]]
    h := ![![![2819, -177, 0], ![9298, -1, 0]], ![![861, -54, 0], ![2840, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {2187} * I53N1 =  Ideal.span {B.equivFun.symm ![639, -67, -1]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 243 ![![59, 0, 0], ![16, 1, 0]]
  ![-21237867, -5616500, -776168] ![![243, 0, 0], ![-67, 1, 0]] where
    su := ![![14337, 0, 0], ![3888, 243, 0]]
    hsu := by decide
    w := ![![-5160801681, -1364809500, -188608824], ![1269255825, 335663433, 46386756]]
    hw := by decide
    g := ![![![-5554352, -5267590187, 78621980], ![-20145839, -19105142748, 0]], ![![-1661027, -1575282258, 23512044], ![-6024499, -5713427080, 0]]]
    h := ![![![-48792205649, -3402749544, -22085905], ![179919930964, 1302292227, 0]], ![![12000033137, 836877655, 5431842], ![-44249795738, -320287786, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {243} * I59N1 =  Ideal.span {B.equivFun.symm ![-21237867, -5616500, -776168]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E59RS1 


noncomputable def E61RS0 : RelationCertificate Table 27 ![![61, 0, 0], ![7, 1, 0]]
  ![-4869, -1288, -178] ![![27, 0, 0], ![-13, 1, 0]] where
    su := ![![1647, 0, 0], ![189, 27, 0]]
    hsu := by decide
    w := ![![-131463, -34776, -4806], ![28053, 7425, 1026]]
    hw := by decide
    g := ![![![-262747, -18152414, 1397894], ![-545774, -37743144, 0]], ![![-34653, -2394665, 184410], ![-71978, -4979072, 0]]]
    h := ![![![-788996, -114411, -244], ![6874841, 14706, 0]], ![![168352, 24405, 51], ![-1466919, -3073, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {27} * I61N0 =  Ideal.span {B.equivFun.symm ![-4869, -1288, -178]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 9 ![![61, 0, 0], ![-14, 1, 0]]
  ![-81, -25, 5] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![549, 0, 0], ![-126, 9, 0]]
    hsu := by decide
    w := ![![-729, -225, 45], ![1314, 144, -45]]
    hw := by decide
    g := ![![![39383, 957736, -241918], ![88919, 2177217, 0]], ![![-8764, -212835, 53759], ![-19753, -483826, 0]]]
    h := ![![![-10869, 819, -3], ![-47352, 188, 0]], ![![19618, -1458, 4], ![85468, -249, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {9} * I61N1 =  Ideal.span {B.equivFun.symm ![-81, -25, 5]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E61RS1 


noncomputable def E71RS1 : RelationCertificate Table 243 ![![71, 0, 0], ![17, 1, 0]]
  ![83302280595, 22029860906, 3044400104] ![![243, 0, 0], ![-67, 1, 0]] where
    su := ![![17253, 0, 0], ![4131, 243, 0]]
    hsu := by decide
    w := ![![20242454184585, 5353256200158, 739789225272], ![-4978461579273, -1316588397507, -181944946062]]
    hw := by decide
    g := ![![![13438737, 12737195581, -190110833], ![48711140, 46196815911, 0]], ![![3308728, 3137194664, -46824612], ![11998133, 11378360866, 0]]]
    h := ![![![243392123362653, 15413186006264, 64499409186], ![-1016515144498104, -4576413652102, 0]], ![![-59860248357733, -3790743634485, -15863087924], ![250003361523696, 1125530497970, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {243} * I71N1 =  Ideal.span {B.equivFun.symm ![83302280595, 22029860906, 3044400104]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E71RS1 


noncomputable def E79RS1 : RelationCertificate Table 3 ![![79, 0, 0], ![10, 1, 0]]
  ![6485, 1715, 237] ![![3, 0, 0], ![-18, -1, 1]] where
    su := ![![237, 0, 0], ![30, 3, 0]]
    hsu := by decide
    w := ![![19455, 5145, 711], ![175914, 46521, 6429]]
    hw := by decide
    g := ![![![17, -92, 6], ![37, 0, 0]], ![![2, -11, 2], ![-3, 0, 0]]]
    h := ![![![6475, 671, 4], ![-50504, -79, 0]], ![![58642, 6075, 36], ![-457408, -701, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {3} * I79N1 =  Ideal.span {B.equivFun.symm ![6485, 1715, 237]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS1 
