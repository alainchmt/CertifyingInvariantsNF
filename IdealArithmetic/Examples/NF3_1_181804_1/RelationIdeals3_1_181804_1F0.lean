import IdealArithmetic.Examples.NF3_1_181804_1.PrimesBelow3_1_181804_1F0
import IdealArithmetic.Examples.NF3_1_181804_1.ClassGroupData3_1_181804_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 27 ![![3, 0, 0], ![2, -1, 1]]
  ![-1, -16, 4] ![![27, 0, 0], ![4, 1, 0]] where
    su := ![![81, 0, 0], ![54, -27, 27]]
    hsu := by decide
    w := ![![-27, -432, 108], ![324, -81, 0]]
    hw := by decide
    g := ![![![-3, -100, -25], ![0, 671, 0]], ![![-14, -68, -17], ![-1, 440, 0]]]
    h := ![![![-3, -4, 0], ![4, 0, 0]], ![![2, 0, -1], ![3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {27} * I3N0 =  Ideal.span {B.equivFun.symm ![-1, -16, 4]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 9 ![![7, 0, 0], ![2, 1, 0]]
  ![-569, -113, -28] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![63, 0, 0], ![18, 9, 0]]
    hsu := by decide
    w := ![![-5121, -1017, -252], ![-4572, -909, -225]]
    hw := by decide
    g := ![![![-5, -29, -7], ![-2, 66, 0]], ![![0, -14, -3], ![5, 28, 0]]]
    h := ![![![-7079, -3875, -184], ![24492, 1260, 0]], ![![-6320, -3461, -165], ![21866, 1130, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {9} * I7N0 =  Ideal.span {B.equivFun.symm ![-569, -113, -28]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 297 ![![7, 0, 0], ![-1, 1, 0]]
  ![-89, 7, 5] ![![297, 0, 0], ![58, 1, 0]] where
    su := ![![2079, 0, 0], ![-297, 297, 0]]
    hsu := by decide
    w := ![![-26433, 2079, 1485], ![-4752, 297, 297]]
    hw := by decide
    g := ![![![-37, 5277, 91], ![190, -27025, 0]], ![![-47, -697, -12], ![241, 3565, 0]]]
    h := ![![![-26, 15, 0], ![-93, 5, 0]], ![![-4, 2, 0], ![-12, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {297} * I7N1 =  Ideal.span {B.equivFun.symm ![-89, 7, 5]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 1 ![![11, 0, 0], ![3, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![3, 1, 0]] where
    su := ![![11, 0, 0], ![3, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![3, 1, 0]]
    hw := by decide
    g := ![![![7, 2, 0], ![-22, 0, 0]], ![![-3, -1, 0], ![12, 0, 0]]]
    h := ![![![7, 2, 0], ![-22, 0, 0]], ![![-3, -1, 0], ![12, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {1} * I11N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 27 ![![11, 0, 0], ![-2, 1, 0]]
  ![7, 4, -1] ![![27, 0, 0], ![4, 1, 0]] where
    su := ![![297, 0, 0], ![-54, 27, 0]]
    hsu := by decide
    w := ![![189, 108, -27], ![-54, 27, 0]]
    hw := by decide
    g := ![![![29, -5965, -1493], ![-191, 40312, 0]], ![![-12, 1613, 404], ![82, -10908, 0]]]
    h := ![![![425, -216, 2], ![2334, -23, 0]], ![![-122, 63, -1], ![-670, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {27} * I11N1 =  Ideal.span {B.equivFun.symm ![7, 4, -1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 33 ![![11, 0, 0], ![-1, 1, 0]]
  ![-37, 17, -2] ![![33, 0, 0], ![-8, 1, 0]] where
    su := ![![363, 0, 0], ![-33, 33, 0]]
    hsu := by decide
    w := ![![-1221, 561, -66], ![132, -165, 33]]
    hw := by decide
    g := ![![![-1336785, -192663841, 24103867], ![-5514220, -795427618, 0]], ![![243073, 35032159, -4382818], ![1002681, 144632992, 0]]]
    h := ![![![-6, 5, -1], ![-29, 9, 0]], ![![2, -2, 0], ![18, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {33} * I11N2 =  Ideal.span {B.equivFun.symm ![-37, 17, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS2 


noncomputable def E17RS1 : RelationCertificate Table 99 ![![17, 0, 0], ![-7, 1, 0]]
  ![329, 62, 16] ![![99, 0, 0], ![-41, 1, 0]] where
    su := ![![1683, 0, 0], ![-693, 99, 0]]
    hsu := by decide
    w := ![![32571, 6138, 1584], ![-12177, -2277, -594]]
    hw := by decide
    g := ![![![58, 8033, -196], ![139, 19400, 0]], ![![-7, -3197, 78], ![-16, -7720, 0]]]
    h := ![![![1022, -154, 3], ![2435, -35, 0]], ![![-370, 62, -2], ![-881, 28, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {99} * I17N1 =  Ideal.span {B.equivFun.symm ![329, 62, 16]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E17RS1 


noncomputable def E23RS1 : RelationCertificate Table 33 ![![23, 0, 0], ![6, 1, 0]]
  ![-35, -8, -1] ![![33, 0, 0], ![-8, 1, 0]] where
    su := ![![759, 0, 0], ![198, 33, 0]]
    hsu := by decide
    w := ![![-1155, -264, -33], ![198, 33, 0]]
    hw := by decide
    g := ![![![-19641, -2831697, 354269], ![-81017, -11690878, 0]], ![![-5552, -800394, 100136], ![-22901, -3304488, 0]]]
    h := ![![![-37, -12, -1], ![136, 22, 0]], ![![-6, -1, 0], ![24, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {33} * I23N1 =  Ideal.span {B.equivFun.symm ![-35, -8, -1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 27 ![![29, 0, 0], ![1, 1, 0]]
  ![109, -11, -4] ![![27, 0, 0], ![4, 1, 0]] where
    su := ![![783, 0, 0], ![27, 27, 0]]
    hsu := by decide
    w := ![![2943, -297, -108], ![108, 81, -27]]
    hw := by decide
    g := ![![![2887, -540934, -135415], ![-19603, 3656182, 0]], ![![265, -50029, -12524], ![-1809, 338144, 0]]]
    h := ![![![6, 1, -1], ![-65, 25, 0]], ![![0, 0, 0], ![4, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {27} * I29N1 =  Ideal.span {B.equivFun.symm ![109, -11, -4]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 33 ![![31, 0, 0], ![11, 1, 0]]
  ![169, -50, 2] ![![33, 0, 0], ![-8, 1, 0]] where
    su := ![![1023, 0, 0], ![363, 33, 0]]
    hsu := by decide
    w := ![![5577, -1650, 66], ![-1188, 561, -66]]
    hw := by decide
    g := ![![![48623, 7012453, -877320], ![200737, 28951494, 0]], ![![18815, 2713442, -339476], ![77693, 11202676, 0]]]
    h := ![![![39246, 4170, 55], ![-110587, -1703, 0]], ![![-8320, -887, -12], ![23444, 370, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {33} * I31N1 =  Ideal.span {B.equivFun.symm ![169, -50, 2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E31RS1 
