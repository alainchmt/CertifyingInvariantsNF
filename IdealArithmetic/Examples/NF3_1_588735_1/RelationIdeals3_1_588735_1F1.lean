import IdealArithmetic.Examples.NF3_1_588735_1.PrimesBelow3_1_588735_1F1
import IdealArithmetic.Examples.NF3_1_588735_1.ClassGroupData3_1_588735_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 5 ![![37, 0, 0], ![4, 1, 0]]
  ![4, 1, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![185, 0, 0], ![20, 5, 0]]
    hsu := by decide
    w := ![![20, 5, 0], ![10, 5, 5]]
    hw := by decide
    g := ![![![844417, -555387, 51005], ![226694, 0, -85008]], ![![91783, -60369, 5544], ![24645, 0, -9240]]]
    h := ![![![1048, 1597, 2670], ![186, -19758, 0]], ![![518, 791, 1323], ![104, -9790, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {5} * I37N0 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 5 ![![37, 0, 0], ![8, 1, 0]]
  ![761, 4, 25] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![185, 0, 0], ![40, 5, 0]]
    hsu := by decide
    w := ![![3805, 20, 125], ![2905, 15, 95]]
    hw := by decide
    g := ![![![1613644, -1061325, 97469], ![433198, 0, -162448]], ![![385075, -253271, 23260], ![103376, 0, -38766]]]
    h := ![![![-95883, -357825, -256175], ![-30371, 1895700, 0]], ![![-73203, -273190, -195583], ![-23193, 1447318, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {5} * I37N1 =  Ideal.span {B.equivFun.symm ![761, 4, 25]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E37RS1 


noncomputable def E37RS2 : RelationCertificate Table 5 ![![37, 0, 0], ![-12, 1, 0]]
  ![-1676, -9, -55] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![185, 0, 0], ![-60, 5, 0]]
    hsu := by decide
    w := ![![-8380, -45, -275], ![-6395, -35, -210]]
    hw := by decide
    g := ![![![-1335, 877, -79], ![-357, 0, 134]], ![![419, -277, 25], ![116, 0, -42]]]
    h := ![![![424, -3521, 1355], ![-226, -10038, 0]], ![![325, -2687, 1034], ![-168, -7660, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {5} * I37N2 =  Ideal.span {B.equivFun.symm ![-1676, -9, -55]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E37RS2 


noncomputable def E47RS0 : RelationCertificate Table 121 ![![47, 0, 0], ![7, 1, 0]]
  ![-40053, -215, -1315] ![![121, 0, 0], ![-17, 1, 0]] where
    su := ![![5687, 0, 0], ![847, 121, 0]]
    hsu := by decide
    w := ![![-4846413, -26015, -159115], ![608146, 3267, 19965]]
    hw := by decide
    g := ![![![1784, -16539, 4595], ![-376, -111205, 0]], ![![290, -2556, 710], ![46, -17181, 0]]]
    h := ![![![-253502604, -783666720, -654020685], ![-54429431, 6147794176, 0]], ![![31810441, 98337410, 82068945], ![6830057, -771448050, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N0 : Ideal.span {121} * I47N0 =  Ideal.span {B.equivFun.symm ![-40053, -215, -1315]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E47RS0 


noncomputable def E47RS1 : RelationCertificate Table 5 ![![47, 0, 0], ![16, 1, 0]]
  ![154, 1, 5] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![235, 0, 0], ![80, 5, 0]]
    hsu := by decide
    w := ![![770, 5, 25], ![585, 5, 20]]
    hw := by decide
    g := ![![![1259469, -828376, 76075], ![338114, 0, -126792]], ![![443145, -291466, 26767], ![118969, 0, -44612]]]
    h := ![![![340, 3085, 1030], ![221, -9681, 0]], ![![255, 2342, 782], ![177, -7350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {5} * I47N1 =  Ideal.span {B.equivFun.symm ![154, 1, 5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS1 


noncomputable def E47RS2 : RelationCertificate Table 275 ![![47, 0, 0], ![-23, 1, 0]]
  ![51, -1, 10] ![![275, 0, 0], ![27, 1, 0]] where
    su := ![![12925, 0, 0], ![-6325, 275, 0]]
    hsu := by decide
    w := ![![14025, -275, 2750], ![1925, -275, 275]]
    hw := by decide
    g := ![![![-345227, -4552637, -875520], ![-50429, 48154621, -182]], ![![155468, 2050231, 394281], ![22723, -21685915, 82]]]
    h := ![![![-39975, 678813, -141570], ![34028, 1330760, 0]], ![![-5816, 98856, -20617], ![4967, 193800, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N2 : Ideal.span {275} * I47N2 =  Ideal.span {B.equivFun.symm ![51, -1, 10]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E47RS2 


noncomputable def E53RS0 : RelationCertificate Table 25 ![![53, 0, 0], ![8, 1, 0]]
  ![-2586, -14, -85] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![1325, 0, 0], ![200, 25, 0]]
    hsu := by decide
    w := ![![-64650, -350, -2125], ![-9875, -50, -325]]
    hw := by decide
    g := ![![![-182483233, -88895395, -454350856], ![-18154454, 2271142220, 1020096]], ![![-31993814, -15585556, -79658915], ![-3182918, 398187266, 178848]]]
    h := ![![![2487378, 8983634, 6424225], ![544998, -68096802, 0]], ![![379941, 1372234, 981289], ![83258, -10401666, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {25} * I53N0 =  Ideal.span {B.equivFun.symm ![-2586, -14, -85]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 605 ![![53, 0, 0], ![17, 1, 0]]
  ![-8556, -49, -280] ![![605, 0, 0], ![-138, 1, 0]] where
    su := ![![32065, 0, 0], ![10285, 605, 0]]
    hsu := by decide
    w := ![![-5176380, -29645, -169400], ![1165230, 6655, 38115]]
    hw := by decide
    g := ![![![160942950201659109, -12084056228244532300, 434681651853621487], ![-56684600588550599, -52596479875447919612, -42325536]], ![![54257282457130888, -4073791683215685586, 146540405367261872], ![-19109581259999304, -17731389049829652617, -14268836]]]
    h := ![![![223175510, 2067087323, 646616825], ![110586248, -6854138401, 0]], ![![-50238002, -465312375, -145556894], ![-24893538, 1542903089, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {605} * I53N1 =  Ideal.span {B.equivFun.symm ![-8556, -49, -280]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 11 ![![53, 0, 0], ![-25, 1, 0]]
  ![15, 1, 1] ![![11, 0, 0], ![5, 1, 0]] where
    su := ![![583, 0, 0], ![-275, 11, 0]]
    hsu := by decide
    w := ![![165, 11, 11], ![132, -11, 11]]
    hw := by decide
    g := ![![![191858, 491641, 629542], ![131916, -1384992, 0]], ![![-86162, -220784, -282711], ![-59232, 621964, 0]]]
    h := ![![![300, -5284, 1017], ![-227, -10780, 0]], ![![244, -4245, 817], ![-176, -8660, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {11} * I53N2 =  Ideal.span {B.equivFun.symm ![15, 1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS2 


noncomputable def E59RS0 : RelationCertificate Table 605 ![![59, 0, 0], ![-29, 1, 0]]
  ![443, -233, -35] ![![605, 0, 0], ![-138, 1, 0]] where
    su := ![![35695, 0, 0], ![-17545, 605, 0]]
    hsu := by decide
    w := ![![268015, -140965, -21175], ![-63525, 33880, 3630]]
    hw := by decide
    g := ![![![120179535305742122, -9023422649341686413, 324586065180267723], ![-42327600862039311, -39274913888137635435, -48366454]], ![![-58537633438347708, 4395172656165288960, -158100961651915630], ![20617134001086537, 19130216360527296045, 23558568]]]
    h := ![![![-953623, 20281281, -3382510], ![812518, 39913611, 0]], ![![226694, -4821109, 804064], ![-193133, -9487954, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {605} * I59N0 =  Ideal.span {B.equivFun.symm ![443, -233, -35]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 11 ![![59, 0, 0], ![-17, 1, 0]]
  ![-7, 1, 1] ![![11, 0, 0], ![5, 1, 0]] where
    su := ![![649, 0, 0], ![-187, 11, 0]]
    hsu := by decide
    w := ![![-77, 11, 11], ![22, -33, 11]]
    hw := by decide
    g := ![![![317, 848, 1086], ![231, -2390, 0]], ![![-94, -242, -309], ![-58, 680, 0]]]
    h := ![![![-6915, 70545, -19611], ![3226, 231410, 0]], ![![2038, -20681, 5749], ![-908, -67838, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {11} * I59N1 =  Ideal.span {B.equivFun.symm ![-7, 1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E59RS1 


noncomputable def E59RS2 : RelationCertificate Table 25 ![![59, 0, 0], ![-13, 1, 0]]
  ![148, 2, 5] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![1475, 0, 0], ![-325, 25, 0]]
    hsu := by decide
    w := ![![3700, 50, 125], ![575, 0, 25]]
    hw := by decide
    g := ![![![64133390750, 32065389616, 161613079907], ![6413286865, -808065058902, -567721]], ![![-13326422431, -6662939889, -33581947685], ![-1332631378, 167909667644, 117968]]]
    h := ![![![-998, 7568, -2705], ![370, 31920, 0]], ![![-144, 1177, -421], ![109, 4968, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N2 : Ideal.span {25} * I59N2 =  Ideal.span {B.equivFun.symm ![148, 2, 5]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E59RS2 


noncomputable def E61RS1 : RelationCertificate Table 121 ![![61, 0, 0], ![-15, 1, 0]]
  ![-708, -1, -23] ![![121, 0, 0], ![-17, 1, 0]] where
    su := ![![7381, 0, 0], ![-1815, 121, 0]]
    hsu := by decide
    w := ![![-85668, -121, -2783], ![10769, 0, 363]]
    hw := by decide
    g := ![![![53458403, -495706810, 137722983], ![-11607390, -3332896188, 0]], ![![-13106752, 121535833, -33766487], ![2845940, 817148985, 0]]]
    h := ![![![2368, -20777, 6497], ![-892, -79268, 0]], ![![-287, 2612, -817], ![156, 9968, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {121} * I61N1 =  Ideal.span {B.equivFun.symm ![-708, -1, -23]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 11 ![![67, 0, 0], ![-28, 1, 0]]
  ![10814, 58, 355] ![![11, 0, 0], ![5, 1, 0]] where
    su := ![![737, 0, 0], ![-308, 11, 0]]
    hsu := by decide
    w := ![![118954, 638, 3905], ![73711, 396, 2420]]
    hw := by decide
    g := ![![![663316, 1699732, 2176490], ![456035, -4788282, 0]], ![![-273860, -701750, -898585], ![-188274, 1976888, 0]]]
    h := ![![![9760506, -182661414, 31510865], ![-6805284, -422245520, 0]], ![![6048199, -113187899, 19526010], ![-4216941, -261648490, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {11} * I67N1 =  Ideal.span {B.equivFun.symm ![10814, 58, 355]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 55 ![![71, 0, 0], ![28, 1, 0]]
  ![-133, 63, 30] ![![55, 0, 0], ![27, 1, 0]] where
    su := ![![3905, 0, 0], ![1540, 55, 0]]
    hsu := by decide
    w := ![![-7315, 3465, 1650], ![-1815, 605, 1155]]
    hw := by decide
    g := ![![![-30027803761, -547505252666, -105376263284], ![-24695562760, 1159134851157, 722351]], ![![-14608121091, -266353912556, -51264129212], ![-12014057854, 563903453497, 351414]]]
    h := ![![![390033, 6573890, 1218030], ![246413, -17296020, 0]], ![![96357, 1624276, 300951], ![60915, -4273500, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {55} * I71N1 =  Ideal.span {B.equivFun.symm ![-133, 63, 30]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 11 ![![73, 0, 0], ![-33, 1, 0]]
  ![-3, 2, 2] ![![11, 0, 0], ![5, 1, 0]] where
    su := ![![803, 0, 0], ![-363, 11, 0]]
    hsu := by decide
    w := ![![-33, 22, 22], ![99, -55, 22]]
    hw := by decide
    g := ![![![660410, 1692223, 2166874], ![454029, -4767120, 0]], ![![-298411, -764635, -979106], ![-205144, 2154032, 0]]]
    h := ![![![-2044, 47075, -6926], ![1607, 101120, 0]], ![![6175, -140859, 20724], ![-4678, -302570, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {11} * I73N1 =  Ideal.span {B.equivFun.symm ![-3, 2, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E73RS1 
