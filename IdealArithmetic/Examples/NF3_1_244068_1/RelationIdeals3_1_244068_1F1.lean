import IdealArithmetic.Examples.NF3_1_244068_1.PrimesBelow3_1_244068_1F1
import IdealArithmetic.Examples.NF3_1_244068_1.ClassGroupData3_1_244068_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 3 ![![37, 0, 0], ![4, 1, 0]]
  ![25358446410923, 321104463602, 1157555056719] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![111, 0, 0], ![12, 3, 0]]
    hsu := by decide
    w := ![![76075339232769, 963313390806, 3472665170157], ![362471031283992, 4589834258205, 16545973218462]]
    hw := by decide
    g := ![![![22179, -432778, 377275], ![85034, 0, 12]], ![![30848, -294911, -43132], ![31296, 0, 3]]]
    h := ![![![3877941672754563, 9859946691024858, 11854196532193575], ![685721983298486, -73100685689350926, 0]], ![![18476966801050354, 46979022131806799, 56480889673331940], ![3267213225297527, -348297900431479271, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {3} * I37N0 =  Ideal.span {B.equivFun.symm ![25358446410923, 321104463602, 1157555056719]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 3 ![![37, 0, 0], ![7, 1, 0]]
  ![105685, -689732, -951612] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![111, 0, 0], ![21, 3, 0]]
    hsu := by decide
    w := ![![317055, -2069196, -2854836], ![-11459346, 20159601, 5221533]]
    hw := by decide
    g := ![![![2582348036727, -2900205593371, -1168798977615], ![10694622647741, 0, 13612]], ![![534922453123, -600765298291, -242111754980], ![2215345763544, 0, 2988]]]
    h := ![![![-2066107, -8752336, -6588708], ![-627412, 40471764, 0]], ![![58852978, 249043301, 187055437], ![17865274, -1153218443, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {3} * I37N1 =  Ideal.span {B.equivFun.symm ![105685, -689732, -951612]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E37RS2 : RelationCertificate Table 3 ![![37, 0, 0], ![-11, 1, 0]]
  ![1138608823, -901635290, 1456341576] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![111, 0, 0], ![-33, 3, 0]]
    hsu := by decide
    w := ![![3415826469, -2704905870, 4369024728], ![4427042034, -15851409363, -16476641811]]
    hw := by decide
    g := ![![![-6287555386004930001, 7061481813857859337, 2845816457077894286], ![-26039492377711088777, 0, -39]], ![![1756370273321428505, -1972559441951944113, -794952429312342197], ![7273890651745237644, 0, 9]]]
    h := ![![![-55622704609, 314794358738, -189258001752], ![25044435404, 1167333734400, 0]], ![![-90727841331, 513309438722, -308882158311], ![40846370115, 1903857940595, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {3} * I37N2 =  Ideal.span {B.equivFun.symm ![1138608823, -901635290, 1456341576]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS2 


noncomputable def E53RS1 : RelationCertificate Table 3 ![![53, 0, 0], ![-20, 1, 0]]
  ![13427005, -19860158, 626325] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![159, 0, 0], ![-60, 3, 0]]
    hsu := by decide
    w := ![![40281015, -59580474, 1878975], ![-128531808, 142426911, -91510710]]
    hw := by decide
    g := ![![![-286398083408921, 321650424268468, 129626910461456], ![-1186098610998284, 0, 143]], ![![104484541980470, -117345398605660, -47290848481591], ![432715780213149, 0, -51]]]
    h := ![![![2710451947, -31515101408, 9961667931], ![-1617436591, -87994629003, 0]], ![![-8579691730, 99757840918, -31533274264], ![5119842986, 278538838737, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {3} * I53N1 =  Ideal.span {B.equivFun.symm ![13427005, -19860158, 626325]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 3 ![![61, 0, 0], ![14, 1, 0]]
  ![8903655, -62073552, -87281936] ![![3, 0, 0], ![16, 0, 1]] where
    su := ![![183, 0, 0], ![42, 3, 0]]
    hsu := by decide
    w := ![![26710965, -186220656, -261845808], ![320811984, -151250304, 594668823]]
    hw := by decide
    g := ![![![45972763108269931, 16704875153659280, -19358695908435581], ![238735171274627815, 0, 0]], ![![11051847137192386, 4015850128680103, -4653828342915832], ![57391908617387512, 0, 0]]]
    h := ![![![44586265, 359786885, 142996720], ![16131103, -1468346976, 0]], ![![472343106, 3820195631, 1532779937], ![171032781, -15550225536, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {3} * I61N1 =  Ideal.span {B.equivFun.symm ![8903655, -62073552, -87281936]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E61RS1 


noncomputable def E67RS1 : RelationCertificate Table 3 ![![67, 0, 0], ![-22, 1, 0]]
  ![-337213, -4270, -15393] ![![3, 0, 0], ![14, 1, 1]] where
    su := ![![201, 0, 0], ![-66, 3, 0]]
    hsu := by decide
    w := ![![-1011639, -12810, -46179], ![-4820088, -61035, -220026]]
    hw := by decide
    g := ![![![8279, -73925, -41536], ![211, 0, -13846]], ![![-2530, 22474, 12636], ![-59, 0, 4214]]]
    h := ![![![124215, -1577817, 450831], ![-64276, -5036845, 0]], ![![591772, -7517715, 2148044], ![-306455, -23998715, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3} * I67N1 =  Ideal.span {B.equivFun.symm ![-337213, -4270, -15393]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS1 


noncomputable def E71RS0 : RelationCertificate Table 3 ![![71, 0, 0], ![15, 1, 0]]
  ![3631425147, 45983370, 165766249] ![![3, 0, 0], ![16, 0, 1]] where
    su := ![![213, 0, 0], ![45, 3, 0]]
    hsu := by decide
    w := ![![10894275441, 137950110, 497298747], ![56757374544, 718697274, 2590844283]]
    hw := by decide
    g := ![![![877, -22828, -7549], ![2206, 0, 0]], ![![215, -2855, -3302], ![88, 0, 0]]]
    h := ![![![-333922169052, -2857481448497, -1072138626433], ![-110793154655, 12687001373832, 0]], ![![-1739679313194, -14887006088948, -5585665050705], ![-577214025110, 66097180369136, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {3} * I71N0 =  Ideal.span {B.equivFun.symm ![3631425147, 45983370, 165766249]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 3 ![![71, 0, 0], ![26, 1, 0]]
  ![635, 8, 29] ![![3, 0, 0], ![16, 0, 1]] where
    su := ![![213, 0, 0], ![78, 3, 0]]
    hsu := by decide
    w := ![![1905, 24, 87], ![9924, 126, 453]]
    hw := by decide
    g := ![![![-11, 10, 2], ![1, 0, 0]], ![![-12, 3, 1], ![2, 0, 0]]]
    h := ![![![-18657, -306669, -68183], ![-11092, 806837, 0]], ![![-97098, -1597569, -355195], ![-58041, 4203166, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {3} * I71N1 =  Ideal.span {B.equivFun.symm ![635, 8, 29]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 3 ![![71, 0, 0], ![30, 1, 0]]
  ![-1784701, 4717892, 3643319] ![![3, 0, 0], ![16, 0, 1]] where
    su := ![![213, 0, 0], ![90, 3, 0]]
    hsu := by decide
    w := ![![-5354103, 14153676, 10929957], ![-6224556, -6447438, -28362507]]
    hw := by decide
    g := ![![![101203372008373, 36773723836174, -42615783154138], ![525546056326663, 0, 0]], ![![43709013998308, 15882308840387, -18405452560211], ![226979590470976, 0, 0]]]
    h := ![![![381887017, 7681254474, 1487467663], ![269547467, -17601093459, 0]], ![![409685254, 8240313401, 1595560349], ![289167281, -18882373158, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {3} * I71N2 =  Ideal.span {B.equivFun.symm ![-1784701, 4717892, 3643319]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS2 


noncomputable def E73RS1 : RelationCertificate Table 3 ![![73, 0, 0], ![-35, 1, 0]]
  ![21, 0, 1] ![![3, 0, 0], ![16, 0, 1]] where
    su := ![![219, 0, 0], ![-105, 3, 0]]
    hsu := by decide
    w := ![![63, 0, 3], ![324, 6, 15]]
    hw := by decide
    g := ![![![-3, 2, 0], ![1, 0, 0]], ![![-1, -1, 0], ![0, 0, 0]]]
    h := ![![![2072, -48637, 8587], ![-1649, -104475, 0]], ![![10654, -249948, 44129], ![-8462, -536902, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {3} * I73N1 =  Ideal.span {B.equivFun.symm ![21, 0, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E73RS1 
