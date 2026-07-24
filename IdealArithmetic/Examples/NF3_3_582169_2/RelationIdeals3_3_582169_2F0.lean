import IdealArithmetic.Examples.NF3_3_582169_2.PrimesBelow3_3_582169_2F0
import IdealArithmetic.Examples.NF3_3_582169_2.ClassGroupData3_3_582169_2

set_option linter.all false

noncomputable section


noncomputable def E5RS0 : RelationCertificate Table 205 ![![5, 0, 0], ![2, 1, 0]]
  ![-648, 39, 4] ![![205, 0, 0], ![-62, 1, 0]] where
    su := ![![1025, 0, 0], ![410, 205, 0]]
    hsu := by decide
    w := ![![-132840, 7995, 820], ![33620, -2050, -205]]
    hw := by decide
    g := ![![![-5228, -3874916, 62500], ![-17289, -12812501, 0]], ![![-10457, -7749832, 125000], ![-34582, -25625002, 0]]]
    h := ![![![-157068, -96141, -8839], ![392346, 44199, 0]], ![![39744, 24326, 2236], ![-99278, -11181, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {205} * I5N0 =  Ideal.span {B.equivFun.symm ![-648, 39, 4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![5, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -1], ![-4, 5, 0]]]
    h := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -1], ![-4, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 25625 ![![5, 0, 0], ![-1, 1, 0]]
  ![31137, -1706, -196] ![![25625, 0, 0], ![10188, 1, 0]] where
    su := ![![128125, 0, 0], ![-25625, 25625, 0]]
    hsu := by decide
    w := ![![797885625, -43716250, -5022500], ![317545000, -17399375, -1998750]]
    hw := by decide
    g := ![![![-19093213522303, 1425124295382827205, 139882636165775], ![48023517521497, -3584492551747984359, 0]], ![![4200506973151, -313527344984196527, -30774179956468], ![-10565173850314, 788588361384492526, 0]]]
    h := ![![![13840, -8173, 180], ![38063, -1096, 0]], ![![5508, -3252, 71], ![15148, -433, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {25625} * I5N2 =  Ideal.span {B.equivFun.symm ![31137, -1706, -196]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 625 ![![7, 0, 0], ![2, 1, 0]]
  ![-3468, 159, 19] ![![625, 0, 0], ![188, 1, 0]] where
    su := ![![4375, 0, 0], ![1250, 625, 0]]
    hsu := by decide
    w := ![![-2167500, 99375, 11875], ![-683125, 31250, 3750]]
    hw := by decide
    g := ![![![26, -265457, -1412], ![-90, 882504, 0]], ![![0, -106598, -567], ![-6, 354382, 0]]]
    h := ![![![-3034176, -1677265, -80221], ![10617882, 561566, 0]], ![![-956283, -528624, -25283], ![3346444, 176987, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {625} * I7N0 =  Ideal.span {B.equivFun.symm ![-3468, 159, 19]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 1025 ![![11, 0, 0], ![0, 1, 0]]
  ![22561, -1243, -138] ![![1025, 0, 0], ![-62, 1, 0]] where
    su := ![![11275, 0, 0], ![0, 1025, 0]]
    hsu := by decide
    w := ![![23125025, -1274075, -141450], ![-1172600, 64575, 7175]]
    hw := by decide
    g := ![![![-152, -3304412, 53297], ![-2532, -54629432, 0]], ![![-1199, -20970303, 338231], ![-19839, -346686780, 0]]]
    h := ![![![2051, -113, 0], ![0, -138, 0]], ![![-104, 5, 0], ![8, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {1025} * I11N0 =  Ideal.span {B.equivFun.symm ![22561, -1243, -138]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 128125 ![![11, 0, 0], ![3, 1, 0]]
  ![10741, -1158, -103] ![![128125, 0, 0], ![-41062, 1, 0]] where
    su := ![![1409375, 0, 0], ![384375, 128125, 0]]
    hsu := by decide
    w := ![![1376190625, -148368750, -13196875], ![-440878125, 47534375, 4228125]]
    hw := by decide
    g := ![![![13169, 77689304, -1892], ![41091, 242412501, 0]], ![![39474, 22584100, -550], ![123170, 70468753, 0]]]
    h := ![![![10355, 3295, 82], ![-34388, -1005, 0]], ![![-3321, -1059, -27], ![11030, 330, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {128125} * I11N1 =  Ideal.span {B.equivFun.symm ![10741, -1158, -103]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 3125 ![![11, 0, 0], ![-4, 1, 0]]
  ![-4509, 217, 22] ![![3125, 0, 0], ![-437, 1, 0]] where
    su := ![![34375, 0, 0], ![-12500, 3125, 0]]
    hsu := by decide
    w := ![![-14090625, 678125, 68750], ![1934375, -93750, -9375]]
    hw := by decide
    g := ![![![-3924821, -89424424547, 204632571], ![-28066515, -639476784384, 0]], ![![108938, 2478587275, -5671825], ![779017, 17724453120, 0]]]
    h := ![![![-7523, 1942, -34], ![-19561, 396, 0]], ![![1037, -265, 4], ![2697, -47, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {3125} * I11N2 =  Ideal.span {B.equivFun.symm ![-4509, 217, 22]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E11RS2 


noncomputable def E31RS0 : RelationCertificate Table 1025 ![![31, 0, 0], ![1, 1, 0]]
  ![-6933, 329, 39] ![![1025, 0, 0], ![-62, 1, 0]] where
    su := ![![31775, 0, 0], ![1025, 1025, 0]]
    hsu := by decide
    w := ![![-7106325, 337225, 39975], ![365925, -17425, -2050]]
    hw := by decide
    g := ![![![21, -543926, 8773], ![362, -8992320, 0]], ![![8, -30380, 490], ![137, -502248, 0]]]
    h := ![![![-448, -214, 1], ![6955, 8, 0]], ![![22, 9, -1], ![-325, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {1025} * I31N0 =  Ideal.span {B.equivFun.symm ![-6933, 329, 39]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 128125 ![![31, 0, 0], ![5, 1, 0]]
  ![-123462, 5056, 671] ![![128125, 0, 0], ![-41062, 1, 0]] where
    su := ![![3971875, 0, 0], ![640625, 128125, 0]]
    hsu := by decide
    w := ![![-15818568750, 647800000, 85971875], ![5068496875, -207562500, -27546875]]
    hw := by decide
    g := ![![![24169, 15275057, -372], ![75414, 47662480, 0]], ![![19463, 16055238, -391], ![60730, 50096864, 0]]]
    h := ![![![-59026293392, -12205930087, -80134452], ![365962994338, 2484168683, 0]], ![![18912873204, 3910955518, 25676230], ![-117259805953, -795963345, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {128125} * I31N1 =  Ideal.span {B.equivFun.symm ![-123462, 5056, 671]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 3125 ![![31, 0, 0], ![-7, 1, 0]]
  ![12831, -578, -73] ![![3125, 0, 0], ![-437, 1, 0]] where
    su := ![![96875, 0, 0], ![-21875, 3125, 0]]
    hsu := by decide
    w := ![![40096875, -1806250, -228125], ![-5487500, 246875, 31250]]
    hw := by decide
    g := ![![![939, 14617209, -33449], ![6710, 104528112, 0]], ![![-63, -2910420, 6660], ![-451, -20812501, 0]]]
    h := ![![![34412, -5053, 23], ![150563, -786, 0]], ![![-4706, 697, -4], ![-20590, 134, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {3125} * I31N2 =  Ideal.span {B.equivFun.symm ![12831, -578, -73]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E31RS2 
