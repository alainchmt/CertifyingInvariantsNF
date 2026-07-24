import IdealArithmetic.Examples.NF3_1_644799_1.PrimesBelow3_1_644799_1F4
import IdealArithmetic.Examples.NF3_1_644799_1.ClassGroupData3_1_644799_1

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 6875 ![![197, 0, 0], ![-37, 1, 0]]
  ![-26, 20, 7] ![![6875, 0, 0], ![1688, 454, 1]] where
    su := ![![1354375, 0, 0], ![-254375, 6875, 0]]
    hsu := by decide
    w := ![![-178750, 137500, 48125], ![-570625, 6875, 103125]]
    hw := by decide
    g := ![![![-962, -551, -1006], ![5437, 1690, 0]], ![![-1111, -253, 157], ![4287, -265, 0]]]
    h := ![![![-5409, -72045, 16625], ![707, -363902, 0]], ![![-17198, -229032, 52851], ![2233, -1156848, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {6875} * I197N1 =  Ideal.span {B.equivFun.symm ![-26, 20, 7]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E197RS1 


noncomputable def E211RS1 : RelationCertificate Table 11 ![![211, 0, 0], ![-70, 1, 0]]
  ![6902, -806, 511] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![2321, 0, 0], ![-770, 11, 0]]
    hsu := by decide
    w := ![![75922, -8866, 5621], ![-91102, 10637, -6743]]
    hw := by decide
    g := ![![![-649, -826, 1820], ![51, -2231, 0]], ![![219, 269, -596], ![-4, 730, 0]]]
    h := ![![![19234, 491834, -61475], ![-3892, 1441304, 0]], ![![-22995, -590170, 73766], ![4925, -1729471, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {11} * I211N1 =  Ideal.span {B.equivFun.symm ![6902, -806, 511]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E211RS1 


noncomputable def E223RS1 : RelationCertificate Table 125 ![![223, 0, 0], ![61, 1, 0]]
  ![-2, -3, -2] ![![125, 0, 0], ![-62, -46, 1]] where
    su := ![![27875, 0, 0], ![7625, 125, 0]]
    hsu := by decide
    w := ![![-250, -375, -250], ![-14000, 125, 1625]]
    hw := by decide
    g := ![![![59, 37, 0], ![103, 0, 0]], ![![14, 9, 0], ![25, 0, 0]]]
    h := ![![![-133, 1894, 289], ![134, -7161, 0]], ![![-5253, 107488, 16396], ![-778, -406255, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {125} * I223N1 =  Ideal.span {B.equivFun.symm ![-2, -3, -2]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E223RS1 
