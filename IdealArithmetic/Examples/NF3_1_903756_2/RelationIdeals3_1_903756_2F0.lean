import IdealArithmetic.Examples.NF3_1_903756_2.PrimesBelow3_1_903756_2F0
import IdealArithmetic.Examples.NF3_1_903756_2.ClassGroupData3_1_903756_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 9 ![![2, 0, 0], ![1, 1, 0]]
  ![-936023999, -3650391, 45121168] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![18, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![-8424215991, -32853519, 406090512], ![11050644177, -692166204, -40154301]]
    hw := by decide
    g := ![![![4462250275783022, 570014481929259, 387381808314549], ![-1424081816157749, 1106, 0]], ![![35012812807022253, 4472588743256510, 3039571046253090], ![-11173983297534464, 790, 0]]]
    h := ![![![-28127820639, 11964244505, -87154371764], ![-8081788065, 15850351336, 0]], ![![39334524936, -16770013551, 121992521497], ![11282255693, -22180864053, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {9} * I2N0 =  Ideal.span {B.equivFun.symm ![-936023999, -3650391, 45121168]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![9, -4, 22], ![0, -6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![9, -4, 22], ![0, -6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![1, 1, 0]]
  ![18862931, 1573329, 1480097] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![9, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![56588793, 4719987, 4440291], ![277151067, 23116758, 21746910]]
    hw := by decide
    g := ![![![1486, 133, 430], ![46, -182, 0]], ![![-13530, -142, 1149], ![-47, -130, 0]]]
    h := ![![![27149383, -7429821, 63888573], ![6573190, -17289602, 0]], ![![132967682, -36388524, 312902701], ![32193055, -84678103, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![18862931, 1573329, 1480097]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 9 ![![7, 0, 0], ![2, 1, 0]]
  ![-15179245295, -1266078258, -1191053258] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![63, 0, 0], ![18, 9, 0]]
    hsu := by decide
    w := ![![-136613207655, -11394704322, -10719479322], ![-177489323361, -14804120295, -13926860838]]
    hw := by decide
    g := ![![![-2377, 8835, -26985], ![1776, 24209, 0]], ![![57942, 9690, -15403], ![-18230, 8445, 0]]]
    h := ![![![-96367650429, 3677455060, -280438692812], ![-27008263678, 178352708766, 0]], ![![-125201870023, 4777788485, -364348913885], ![-35089421650, 231717724383, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {9} * I7N0 =  Ideal.span {B.equivFun.symm ![-15179245295, -1266078258, -1191053258]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![5, 1, 0]]
  ![299456920, 24977256, 23497159] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![33, 0, 0], ![15, 3, 0]]
    hsu := by decide
    w := ![![898370760, 74931768, 70491477], ![4399889121, 366988203, 345241293]]
    hw := by decide
    g := ![![![-19920, -1278, 1859], ![-424, 0, 0]], ![![21367, -1223, -38], ![-406, -8, 0]]]
    h := ![![![1067959284348, -8857838596, 56317711157], ![484630780292, 0, -77433915696]], ![![5230471255411, -43382431183, 275823407965], ![2373543076904, 0, -379242800898]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![299456920, 24977256, 23497159]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![1, 0, 1]]
  ![37518275495110, 3129343518657, 2943905536444] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![33, 0, 0], ![3, 0, 3]]
    hsu := by decide
    w := ![![112554826485330, 9388030555971, 8831716609332], ![551252087243880, 45979116140016, 43254495314559]]
    hw := by decide
    g := ![![![-1967547, -698148, 609351], ![-232715, 0, 0]], ![![-8375401, 516600, -2659], ![172200, 0, 0]]]
    h := ![![![-99880550649737, -3129343518657, -608796399023], ![-9135395186245, 6258687037314, 0]], ![![-489178152017422, -15326372046672, -2981660548439], ![-44741801142350, 30652744093344, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![37518275495110, 3129343518657, 2943905536444]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 3 ![![11, 0, 0], ![-7, 0, 1]]
  ![-11383, 615, 107] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![33, 0, 0], ![-21, 0, 3]]
    hsu := by decide
    w := ![![-34149, 1845, 321], ![22041, -12078, 7086]]
    hw := by decide
    g := ![![![-8000978, -600615, -627804], ![-200204, 0, 0]], ![![-10861953, -815382, -852293], ![-271792, 0, 0]]]
    h := ![![![203845, -3075, 16363], ![-128226, -17220, 0]], ![![-1338763, 20130, -107094], ![842212, 112728, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {3} * I11N2 =  Ideal.span {B.equivFun.symm ![-11383, 615, 107]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS2 


noncomputable def E17RS0 : RelationCertificate Table 3 ![![17, 0, 0], ![1, 1, 0]]
  ![2472760, -2901159, 1830712] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![51, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![7418280, -8703477, 5492136], ![323415660, 17428638, -26420613]]
    hw := by decide
    g := ![![![63358843572383, 4756200157945, 4971509162088], ![1585400052650, 43, 0]], ![![58487275743048, 4390502958084, 4589257171302], ![1463500986029, 5, 0]]]
    h := ![![![-8682806, 2065032, -24233003], ![-389270, 37617433, 0]], ![![-161241387, 42749961, -462498457], ![-6970073, 713969718, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {3} * I17N0 =  Ideal.span {B.equivFun.symm ![2472760, -2901159, 1830712]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![7, 1, 0]]
  ![-32710240658, 1228133994, 668634301] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![51, 0, 0], ![21, 3, 0]]
    hsu := by decide
    w := ![![-98130721974, 3684401982, 2005902903], ![127272613059, -31823337141, 15515376837]]
    hw := by decide
    g := ![![![57113461781222532546, 4287373958027067856, 4481459611999974491], ![1429124652675689288, 0, 0]], ![![72879784519621308843, 5470914920425617864, 5718578434398530542], ![1823638306808539291, -8, 0]]]
    h := ![![![255686182338, 380279394326, 853014724429], ![127651921812, -1318234698272, 0]], ![![-345684874827, -514538354043, -1152644863481], ![-172607792796, 1781830406496, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![-32710240658, 1228133994, 668634301]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 3 ![![17, 0, 0], ![8, 1, 0]]
  ![-617776771, -51527841, -48474415] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![51, 0, 0], ![24, 3, 0]]
    hsu := by decide
    w := ![![-1853330313, -154583523, -145423245], ![-9076929309, -757093164, -712229496]]
    hw := by decide
    g := ![![![41464, -2676, 88], ![-891, 4, 0]], ![![19916, 1279, -1870], ![427, 3, 0]]]
    h := ![![![-76653960491, -143741593734, -268325571635], ![-44527839843, 414680567580, 0]], ![![-375422867523, -703993387432, -1314159828091], ![-218080960434, 2030952697065, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {3} * I17N2 =  Ideal.span {B.equivFun.symm ![-617776771, -51527841, -48474415]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS2 


noncomputable def E19RS0 : RelationCertificate Table 9 ![![19, 0, 0], ![1, 1, 0]]
  ![-31192440525749, -2601715038930, -2447543154560] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![171, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![-280731964731741, -23415435350370, -22027888391040], ![-364729935862953, -30421581103899, -28618865428230]]
    hw := by decide
    g := ![![![2477255, -159267, 10265], ![-843442, 38425, 0]], ![![576194, 202950, -165560], ![-169511, 15370, 0]]]
    h := ![![![22389848218982, -6200877267837, 66081283066604], ![852051102697, -114362901947276, 0]], ![![29089127462539, -8056245288467, 85853501426726], ![1106993798638, -148581491004024, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {9} * I19N0 =  Ideal.span {B.equivFun.symm ![-31192440525749, -2601715038930, -2447543154560]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 9 ![![19, 0, 0], ![7, 1, 0]]
  ![-38868254937103021364, -3241943294669404083, -3049832898534158492] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![171, 0, 0], ![63, 9, 0]]
    hsu := by decide
    w := ![![-349814294433927192276, -29177489652024636747, -27448496086807426428], ![-454482428799119556276, -37907702956426793409, -35661376241363444913]]
    hw := by decide
    g := ![![![-2418812631, -346296655, 296780223], ![767793472, 14, 0]], ![![1633944780, -69976141, 5102791], ![-552423382, 14, 0]]]
    h := ![![![-13053819838484865595269, -18677549622708965549406, -41761085259372415683198], ![-5792330973268580248219, 72132506372288851256570, 0]], ![![-16959660710552537684307, -24266069887970736247342, -54256443375705336446593], ![-7525457624307289475653, 93715314705751223928510, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {9} * I19N1 =  Ideal.span {B.equivFun.symm ![-38868254937103021364, -3241943294669404083, -3049832898534158492]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 9 ![![19, 0, 0], ![-9, 1, 0]]
  ![-109, -9, 11] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![171, 0, 0], ![-81, 9, 0]]
    hsu := by decide
    w := ![![-981, -81, 99], ![2304, -9, -99]]
    hw := by decide
    g := ![![![36, 167, -330], ![14, 280, 0]], ![![95, -66, 165], ![-31, -132, 0]]]
    h := ![![![-12, 43, -44], ![21, 77, 0]], ![![24, -44, 44], ![-12, -77, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {9} * I19N2 =  Ideal.span {B.equivFun.symm ![-109, -9, 11]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS2 


noncomputable def E23RS0 : RelationCertificate Table 9 ![![23, 0, 0], ![0, 1, 0]]
  ![425, -117, 59] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![207, 0, 0], ![0, 9, 0]]
    hsu := by decide
    w := ![![3825, -1053, 531], ![9054, 1305, -1287]]
    hw := by decide
    g := ![![![-10480, -1314, -961], ![3350, 43, 0]], ![![-6684, -853, -584], ![2140, 3, 0]]]
    h := ![![![-425, 216, -1217], ![15, 2550, 0]], ![![-1006, 530, -2893], ![27, 6036, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {9} * I23N0 =  Ideal.span {B.equivFun.symm ![425, -117, 59]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 9 ![![23, 0, 0], ![6, 1, 0]]
  ![728696, 47439, -65002] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![207, 0, 0], ![54, 9, 0]]
    hsu := by decide
    w := ![![6558264, 426951, -585018], ![-13891698, 166491, 521829]]
    hw := by decide
    g := ![![![-5059379175, -646388091, -439025905], ![1614638832, -163592, 0]], ![![-4551918287, -581493761, -395115327], ![1452695680, -42757, 0]]]
    h := ![![![-893686, -983280, -2745504], ![-275881, 5734690, 0]], ![![1931256, 2128818, 5925865], ![596381, -12385174, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {9} * I23N1 =  Ideal.span {B.equivFun.symm ![728696, 47439, -65002]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 9 ![![23, 0, 0], ![-7, 1, 0]]
  ![45319, 3780, 3556] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![207, 0, 0], ![-63, 9, 0]]
    hsu := by decide
    w := ![![407871, 34020, 32004], ![529911, 44199, 41580]]
    hw := by decide
    g := ![![![-105, -59, 123], ![38, -93, 0]], ![![34888541, -48821509, 111576094], ![-17054122, -91289534, 0]]]
    h := ![![![273061, -682103, 840029], ![-112760, -1756101, 0]], ![![354767, -886197, 1091376], ![-146490, -2281548, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {9} * I23N2 =  Ideal.span {B.equivFun.symm ![45319, 3780, 3556]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS2 
