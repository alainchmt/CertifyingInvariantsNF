import IdealArithmetic.Examples.NF3_1_329427_1.PrimesBelow3_1_329427_1F1
import IdealArithmetic.Examples.NF3_1_329427_1.ClassGroupData3_1_329427_1

set_option linter.all false

noncomputable section


noncomputable def E43RS1 : RelationCertificate Table 20 ![![43, 0, 0], ![-2, 1, 0]]
  ![23, 9, 2] ![![20, 0, 0], ![-8, 1, 0]] where
    su := ![![860, 0, 0], ![-40, 20, 0]]
    hsu := by decide
    w := ![![460, 180, 40], ![40, -20, 0]]
    hw := by decide
    g := ![![![-321237, 1583394, -433190], ![207687, 4656792, 72198]], ![![8, -1, 0], ![19, 0, 0]]]
    h := ![![![1, 11, -22], ![10, 474, 0]], ![![2, 0, -2], ![42, 43, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {20} * I43N1 =  Ideal.span {B.equivFun.symm ![23, 9, 2]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![3, 1, 0]]
  ![3, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![94, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![6, 2, 0], ![0, 4, 2]]
    hw := by decide
    g := ![![![7893, 563, -70], ![283, 0, -141]], ![![337, 24, -3], ![12, 0, -6]]]
    h := ![![![-3, -1, 0], ![48, 0, 0]], ![![0, -2, -1], ![0, 24, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![3, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 10 ![![53, 0, 0], ![-14, 1, 0]]
  ![183, 49, 12] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![530, 0, 0], ![-140, 10, 0]]
    hsu := by decide
    w := ![![1830, 490, 120], ![1710, 450, 110]]
    hw := by decide
    g := ![![![-68009402, 3537052228, 2380707803], ![340103345, -11903538512, -1007]], ![![19247911, -1001050930, -673784158], ![-96255501, 3368920648, 285]]]
    h := ![![![8353, -594, 0], ![31609, 6, 0]], ![![7797, -548, -1], ![29505, 32, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {10} * I53N1 =  Ideal.span {B.equivFun.symm ![183, 49, 12]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS1 


noncomputable def E61RS0 : RelationCertificate Table 2 ![![61, 0, 0], ![5, 1, 0]]
  ![5, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![122, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![10, 2, 0], ![0, 6, 2]]
    hw := by decide
    g := ![![![884521, 63179, -7897], ![31590, 0, -15795]], ![![81649, 5832, -729], ![2916, 0, -1458]]]
    h := ![![![35, 7, 0], ![-426, 0, 0]], ![![0, -3, -1], ![0, 31, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {2} * I61N0 =  Ideal.span {B.equivFun.symm ![5, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![-4, 1, 0]]
  ![-125, -33, -8] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![122, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![-250, -66, -16], ![-896, -238, -58]]
    hw := by decide
    g := ![![![-966177, -69005, 8624], ![-34502, 0, 17253]], ![![40820, 2915, -364], ![1458, 0, -729]]]
    h := ![![![-893, 225, -2], ![-13587, 57, 0]], ![![-3216, 804, -3], ![-48932, 77, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![-125, -33, -8]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 2 ![![61, 0, 0], ![-1, 1, 0]]
  ![-1, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![122, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![-2, 2, 0], ![0, 0, 2]]
    hw := by decide
    g := ![![![51, 0, 0], ![11, 0, -1]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![0, 31, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {2} * I61N2 =  Ideal.span {B.equivFun.symm ![-1, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS2 


noncomputable def E67RS1 : RelationCertificate Table 4 ![![67, 0, 0], ![-6, 1, 0]]
  ![-95, -25, -6] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![268, 0, 0], ![-24, 4, 0]]
    hsu := by decide
    w := ![![-380, -100, -24], ![-672, -180, -44]]
    hw := by decide
    g := ![![![-1872501, -78524396850, -166863992220], ![-19631099209, 333728017875, 66875]], ![![164778, 6910146670, 14684030780], ![1727536670, -29368064502, -5885]]]
    h := ![![![-2183, 368, -2], ![-24361, 64, 0]], ![![-3876, 652, -3], ![-43254, 95, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {4} * I67N1 =  Ideal.span {B.equivFun.symm ![-95, -25, -6]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E67RS1 


noncomputable def E73RS1 : RelationCertificate Table 10 ![![73, 0, 0], ![-11, 1, 0]]
  ![-41, -13, 6] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![730, 0, 0], ![-110, 10, 0]]
    hsu := by decide
    w := ![![-410, -130, 60], ![590, -20, -20]]
    hw := by decide
    g := ![![![736591811, -38418796873, -25858717929], ![-3694561316, 129293486037, 207178]], ![![-103745362, 5411099707, 3642073996], ![520360905, -18210355389, -29180]]]
    h := ![![![-141, 13, 0], ![-932, 3, 0]], ![![219, -20, 0], ![1448, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {10} * I73N1 =  Ideal.span {B.equivFun.symm ![-41, -13, 6]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![-9, 1, 0]]
  ![-9, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![-18, 2, 0]]
    hsu := by decide
    w := ![![-18, 2, 0], ![0, -8, 2]]
    hw := by decide
    g := ![![![-13287, -950, 118], ![-475, 0, 237]], ![![1681, 120, -15], ![60, 0, -30]]]
    h := ![![![-126, 22, -2], ![-1105, 79, 0]], ![![0, 4, -1], ![0, 40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![-9, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS1 
