import IdealArithmetic.Examples.NF3_1_760455_3.PrimesBelow3_1_760455_3F0
import IdealArithmetic.Examples.NF3_1_760455_3.ClassGroupData3_1_760455_3

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 5 ![![3, 0, 0], ![1, 1, 0]]
  ![269, -197, -244] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![15, 0, 0], ![5, 5, 0]]
    hsu := by decide
    w := ![![1345, -985, -1220], ![-9960, 8180, -1135]]
    hw := by decide
    g := ![![![2314154, 180930, 88579], ![-889474, 144, 0]], ![![1722143, 134596, 66034], ![-661936, 24, 0]]]
    h := ![![![-3867, 327, -15304], ![-1178, 6524, 0]], ![![30129, -2523, 118439], ![9205, -50792, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {5} * I3N0 =  Ideal.span {B.equivFun.symm ![269, -197, -244]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 5 ![![5, 0, 0], ![1, 1, 0]]
  ![6483417212, 7160409, 215581053] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![25, 0, 0], ![5, 5, 0]]
    hsu := by decide
    w := ![![32417086060, 35802045, 1077905265], ![-4976014645, -5495605, -165458190]]
    hw := by decide
    g := ![![![605, -227, -2139], ![-287, 738, 0]], ![![-6824, 6262, -1977], ![3986, 369, 0]]]
    h := ![![![-56126232958, 2160078269, -208492352846], ![-10793230936, 148953906469, 0]], ![![8615362795, -331571477, 32003524290], ![1656758264, -22864387584, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {5} * I5N0 =  Ideal.span {B.equivFun.symm ![6483417212, 7160409, 215581053]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![5, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![7, -11, 28], ![-5, -20, 0]], ![![-2, 5, -14], ![6, 10, 0]]]
    h := ![![![7, -11, 28], ![-5, -20, 0]], ![![-2, 5, -14], ![6, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS1 : RelationCertificate Table 5 ![![7, 0, 0], ![20, 0, 1]]
  ![48458059, 53518, 1611286] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![35, 0, 0], ![100, 0, 5]]
    hsu := by decide
    w := ![![242290295, 267590, 8056430], ![-37191500, -41075, -1236660]]
    hw := by decide
    g := ![![![57, 32, -348], ![-12, 322, 0]], ![![-516, 729, -1431], ![357, 920, 0]]]
    h := ![![![696761, 160554, -68110], ![1981020, 107036, 0]], ![![-106970, -24645, 10454], ![-304080, -16430, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {5} * I7N1 =  Ideal.span {B.equivFun.symm ![48458059, 53518, 1611286]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 25 ![![7, 0, 0], ![17, 0, 1]]
  ![33161, -26313, -6801] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![175, 0, 0], ![425, 0, 25]]
    hsu := by decide
    w := ![![829025, -657825, -170025], ![-38975, 53000, -245400]]
    hw := by decide
    g := ![![![-297624088, 3441630, -10908400], ![-95102023, 496, 0]], ![![-727366299, 8411035, -26659139], ![-232420748, 1204, 0]]]
    h := ![![![21056, -52626, -4434], ![50550, -26313, 0]], ![![-1617, 4240, -1128], ![-4040, 2120, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {25} * I7N2 =  Ideal.span {B.equivFun.symm ![33161, -26313, -6801]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS2 


noncomputable def E11RS0 : RelationCertificate Table 25 ![![11, 0, 0], ![21, -3, 1]]
  ![-2188, 1829, -617] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![275, 0, 0], ![525, -75, 25]]
    hsu := by decide
    w := ![![-54700, 45725, -15425], ![-36675, 29125, 7250]]
    hw := by decide
    g := ![![![123943, -1425, 4551], ![39607, -30, 0]], ![![196162, -2252, 7207], ![62704, -62, 0]]]
    h := ![![![-29, 142, -48], ![-89, 0, 0]], ![![-36, 92, 31], ![-51, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {25} * I11N0 =  Ideal.span {B.equivFun.symm ![-2188, 1829, -617]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 5 ![![11, 0, 0], ![-2, 1, 0]]
  ![607558, 671, 20202] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![55, 0, 0], ![-10, 5, 0]]
    hsu := by decide
    w := ![![3037790, 3355, 101010], ![-466300, -515, -15505]]
    hw := by decide
    g := ![![![7, 19, -119], ![4, 90, 0]], ![![13, -14, 0], ![-8, -16, 0]]]
    h := ![![![2661108, -4063894, 9665397], ![-853280, -15185595, 0]], ![![-408478, 623806, -1483636], ![130986, 2330985, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {5} * I11N1 =  Ideal.span {B.equivFun.symm ![607558, 671, 20202]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 5 ![![13, 0, 0], ![26, 1, 1]]
  ![5733, -4484, -1923] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![65, 0, 0], ![130, 5, 5]]
    hsu := by decide
    w := ![![28665, -22420, -9615], ![-91585, 76875, -29465]]
    hw := by decide
    g := ![![![-22453002, -1755410, -859581], ![8630121, -1292, 0]], ![![-47219904, -3692207, -1806586], ![18149526, -3553, 0]]]
    h := ![![![101, -358, -161], ![170, 0, 0]], ![![-309, 1225, -411], ![-550, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {5} * I13N0 =  Ideal.span {B.equivFun.symm ![5733, -4484, -1923]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 25 ![![13, 0, 0], ![5, 1, 0]]
  ![-115208089, -127238, -3830801] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![325, 0, 0], ![125, 25, 0]]
    hsu := by decide
    w := ![![-2880202225, -3180950, -95770025], ![-1063658825, -1174725, -35367875]]
    hw := by decide
    g := ![![![-88, -4, -20], ![-10, 217, 0]], ![![77, -111, 22], ![36, 97, 0]]]
    h := ![![![37682611661, 90221462644, 160772550787], ![21433424694, -298578141576, 0]], ![![13916190359, 33318790643, 59373311005], ![7915364812, -110264922540, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {25} * I13N1 =  Ideal.span {B.equivFun.symm ![-115208089, -127238, -3830801]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 5 ![![17, 0, 0], ![-3, 1, 0]]
  ![-11759, -13, -391] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![85, 0, 0], ![-15, 5, 0]]
    hsu := by decide
    w := ![![-58795, -65, -1955], ![9025, 10, 300]]
    hw := by decide
    g := ![![![8966, -16183, 40958], ![-6822, -29256, 0]], ![![-1428, 2579, -6527], ![1091, 4664, 0]]]
    h := ![![![-1200241, 2504729, -4420271], ![359146, 10734888, 0]], ![![184238, -384475, 678509], ![-55119, -1647799, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {5} * I17N1 =  Ideal.span {B.equivFun.symm ![-11759, -13, -391]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E23RS1 : RelationCertificate Table 25 ![![23, 0, 0], ![-3, 1, 0]]
  ![19, -2, -154] ![![25, 0, 0], ![8, 1, 0]] where
    su := ![![575, 0, 0], ![-75, 25, 0]]
    hsu := by decide
    w := ![![475, -50, -3850], ![-5550, 4625, -1400]]
    hw := by decide
    g := ![![![-355411, -1554300, -1560230], ![-175902, 5576336, 0]], ![![34465, 148212, 148806], ![16975, -531764, 0]]]
    h := ![![![51, -100, 168], ![2, -574, 0]], ![![-601, 1224, -2142], ![153, 7030, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {25} * I23N1 =  Ideal.span {B.equivFun.symm ![19, -2, -154]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 5 ![![29, 0, 0], ![-10, 1, 0]]
  ![-2, 1, 7] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![145, 0, 0], ![-50, 5, 0]]
    hsu := by decide
    w := ![![-10, 5, 35], ![265, -215, 0]]
    hw := by decide
    g := ![![![-1553, -150, 7], ![596, -48, 0]], ![![471, 44, 0], ![-178, 13, 0]]]
    h := ![![![-424, 2786, -1778], ![244, 7367, 0]], ![![11389, -74699, 47677], ![-6481, -197519, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {5} * I29N1 =  Ideal.span {B.equivFun.symm ![-2, 1, 7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 5 ![![31, 0, 0], ![1, 1, 0]]
  ![-62, 51, -8] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![155, 0, 0], ![5, 5, 0]]
    hsu := by decide
    w := ![![-310, 255, -40], ![-70, 25, 365]]
    hw := by decide
    g := ![![![14281, -62698, 154002], ![-18252, -110539, 0]], ![![10, -2677, 6439], ![-538, -4638, 0]]]
    h := ![![![1017, 0, 3572], ![51, -15820, 0]], ![![170, -1, 603], ![36, -2660, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {5} * I31N1 =  Ideal.span {B.equivFun.symm ![-62, 51, -8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
