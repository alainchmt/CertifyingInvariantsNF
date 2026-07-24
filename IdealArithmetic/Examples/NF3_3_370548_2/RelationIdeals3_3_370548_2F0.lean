import IdealArithmetic.Examples.NF3_3_370548_2.PrimesBelow3_3_370548_2F0
import IdealArithmetic.Examples.NF3_3_370548_2.ClassGroupData3_3_370548_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 5 ![![2, 0, 0], ![-32, -2, 1]]
  ![-16, -4, 1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![10, 0, 0], ![-160, -10, 5]]
    hsu := by decide
    w := ![![-80, -20, 5], ![170, 40, -10]]
    hw := by decide
    g := ![![![2, 0, 0], ![1, 0, 0]], ![![-11, -28, 28], ![2, -69, 0]]]
    h := ![![![0, -177, 133], ![311, 0, -36]], ![![33, 356, -267], ![-620, 0, 72]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {5} * I2N0 =  Ideal.span {B.equivFun.symm ![-16, -4, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 25 ![![3, 0, 0], ![0, 1, 0]]
  ![129, 1, -4] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![75, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![3225, 25, -100], ![-2100, -75, 50]]
    hw := by decide
    g := ![![![-69, -4410, 736], ![-129, -9195, 0]], ![![16, -290, 48], ![-5, -613, 0]]]
    h := ![![![43, 0, -2], ![1, 1, 0]], ![![-28, -2, 0], ![3, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {25} * I3N0 =  Ideal.span {B.equivFun.symm ![129, 1, -4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![-31, -4, 1]]
  ![-1033, -227, 58] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![125, 0, 0], ![-775, -100, 25]]
    hsu := by decide
    w := ![![-25825, -5675, 1450], ![20400, 4475, -1150]]
    hw := by decide
    g := ![![![2984179, 191234466, -31913858], ![6216997, 398923219, 0]], ![![-18376151, -1177602579, 196522321], ![-38283538, -2456528997, 0]]]
    h := ![![![-2, -19, 5], ![33, 0, 0]], ![![33, 19, -5], ![-21, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![-1033, -227, 58]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![5, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -2], ![-4, 5, 0]]]
    h := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -2], ![-4, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 5 ![![7, 0, 0], ![-30, -3, 1]]
  ![-4751, -179, 111] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![35, 0, 0], ![-150, -15, 5]]
    hsu := by decide
    w := ![![-23755, -895, 555], ![24820, 935, -580]]
    hw := by decide
    g := ![![![5, 132, -139], ![28, 348, 0]], ![![-60, -678, 697], ![-108, -1740, 0]]]
    h := ![![![-23, 40, -6], ![153, 0, 0]], ![![62, -38, 5], ![-151, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {5} * I7N0 =  Ideal.span {B.equivFun.symm ![-4751, -179, 111]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 25 ![![7, 0, 0], ![-1, 1, 0]]
  ![103, 7, -3] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![175, 0, 0], ![-25, 25, 0]]
    hsu := by decide
    w := ![![2575, 175, -75], ![-1650, -125, 50]]
    hw := by decide
    g := ![![![7, -175, 29], ![15, -363, 0]], ![![5, -43, 7], ![12, -88, 0]]]
    h := ![![![34, -18, -1], ![135, 2, 0]], ![![-20, 11, -2], ![-74, 8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {25} * I7N1 =  Ideal.span {B.equivFun.symm ![103, 7, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 25 ![![11, 0, 0], ![-29, -2, 1]]
  ![133, 27, -8] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![275, 0, 0], ![-725, -50, 25]]
    hsu := by decide
    w := ![![3325, 675, -200], ![-2700, -575, 150]]
    hw := by decide
    g := ![![![-1, -564, 94], ![-9, -1176, 0]], ![![25, 1492, -249], ![63, 3114, 0]]]
    h := ![![![20, 3, -1], ![3, 0, 0]], ![![6, -1, 0], ![6, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {25} * I11N0 =  Ideal.span {B.equivFun.symm ![133, 27, -8]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 5 ![![11, 0, 0], ![4, 1, 0]]
  ![37, 8, -2] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![55, 0, 0], ![20, 5, 0]]
    hsu := by decide
    w := ![![185, 40, -10], ![-350, -75, 20]]
    hw := by decide
    g := ![![![-11, -407, 422], ![-73, -1056, 0]], ![![-8, -139, 144], ![-24, -360, 0]]]
    h := ![![![35, 9, 0], ![-87, -1, 0]], ![![-74, -23, -2], ![186, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {5} * I11N1 =  Ideal.span {B.equivFun.symm ![37, 8, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E19RS1 : RelationCertificate Table 25 ![![19, 0, 0], ![-8, 1, 0]]
  ![563, 22, -13] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![475, 0, 0], ![-200, 25, 0]]
    hsu := by decide
    w := ![![14075, 550, -325], ![-8550, -325, 200]]
    hw := by decide
    g := ![![![-1549, -100029, 16693], ![-3238, -208666, 0]], ![![686, 43431, -7248], ![1438, 90603, 0]]]
    h := ![![![139969, -19554, 515], ![332356, -4899, 0]], ![![-85026, 11883, -314], ![-201894, 2987, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {25} * I19N1 =  Ideal.span {B.equivFun.symm ![563, 22, -13]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 25 ![![23, 0, 0], ![0, 1, 0]]
  ![-23, -12, -2] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![575, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![-575, -300, -50], ![0, 25, 0]]
    hw := by decide
    g := ![![![-1, 12, -2], ![-12, 24, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-1, -2, -2], ![34, 22, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {25} * I23N0 =  Ideal.span {B.equivFun.symm ![-23, -12, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 5 ![![23, 0, 0], ![2, 1, 0]]
  ![53, 12, -3] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![115, 0, 0], ![10, 5, 0]]
    hsu := by decide
    w := ![![265, 60, -15], ![-520, -115, 30]]
    hw := by decide
    g := ![![![-25, -82, 83], ![-5, -206, 0]], ![![2, -8, 8], ![1, -20, 0]]]
    h := ![![![439, 220, 1], ![-5022, -13, 0]], ![![-864, -435, -4], ![9884, 49, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {5} * I23N1 =  Ideal.span {B.equivFun.symm ![53, 12, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 5 ![![29, 0, 0], ![11, 1, 0]]
  ![61, 4, -1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![145, 0, 0], ![55, 5, 0]]
    hsu := by decide
    w := ![![305, 20, -5], ![-260, 5, 10]]
    hw := by decide
    g := ![![![-1975, -29066, 30075], ![-5019, -75192, 0]], ![![-787, -11461, 11857], ![-1977, -29643, 0]]]
    h := ![![![147, 8, -1], ![-382, 14, 0]], ![![-152, -25, -2], ![396, 30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {5} * I29N1 =  Ideal.span {B.equivFun.symm ![61, 4, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 
