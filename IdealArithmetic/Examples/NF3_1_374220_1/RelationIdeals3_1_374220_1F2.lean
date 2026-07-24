import IdealArithmetic.Examples.NF3_1_374220_1.PrimesBelow3_1_374220_1F2
import IdealArithmetic.Examples.NF3_1_374220_1.ClassGroupData3_1_374220_1

set_option linter.all false

noncomputable section


noncomputable def E109RS1 : RelationCertificate Table 25 ![![109, 0, 0], ![-50, 1, 0]]
  ![25, 4, 1] ![![25, 0, 0], ![9, -4, 1]] where
    su := ![![2725, 0, 0], ![-1250, 25, 0]]
    hsu := by decide
    w := ![![625, 100, 25], ![225, 50, 0]]
    hw := by decide
    g := ![![![-8, 2, 0], ![9, 0, 0]], ![![-5, 3, -1], ![21, 0, 0]]]
    h := ![![![525, -10, 0], ![1144, 1, 0]], ![![201, -4, 0], ![438, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {25} * I109N1 =  Ideal.span {B.equivFun.symm ![25, 4, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E109RS1 


noncomputable def E127RS0 : RelationCertificate Table 125 ![![127, 0, 0], ![-61, 1, 0]]
  ![-1, 15, -4] ![![125, 0, 0], ![34, -4, 1]] where
    su := ![![15875, 0, 0], ![-7625, 125, 0]]
    hsu := by decide
    w := ![![-125, 1875, -500], ![3500, -500, -125]]
    hw := by decide
    g := ![![![91, 19, 3], ![134, 0, 0]], ![![-63, -6, -2], ![20, 0, 0]]]
    h := ![![![12, 59, -1], ![25, 123, 0]], ![![640, -11, 0], ![1332, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N0 : Ideal.span {125} * I127N0 =  Ideal.span {B.equivFun.symm ![-1, 15, -4]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E127RS0 


noncomputable def E127RS1 : RelationCertificate Table 125 ![![127, 0, 0], ![-45, 1, 0]]
  ![-37663, -4388, -1204] ![![125, 0, 0], ![-16, 21, 1]] where
    su := ![![15875, 0, 0], ![-5625, 125, 0]]
    hsu := by decide
    w := ![![-4707875, -548500, -150500], ![-2780000, -323875, -88875]]
    hw := by decide
    g := ![![![-1109, 298, -212], ![310, 1234, 0]], ![![399, -119, 74], ![-24, -434, 0]]]
    h := ![![![-891259, 21363, -45], ![-2514494, 4511, 0]], ![![-526240, 12633, -27], ![-1484672, 2718, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {125} * I127N1 =  Ideal.span {B.equivFun.symm ![-37663, -4388, -1204]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E127RS1 


noncomputable def E127RS2 : RelationCertificate Table 625 ![![127, 0, 0], ![-21, 1, 0]]
  ![-59, -14, 8] ![![625, 0, 0], ![159, 121, 1]] where
    su := ![![79375, 0, 0], ![-13125, 625, 0]]
    hsu := by decide
    w := ![![-36875, -8750, 5000], ![99375, -25625, -625]]
    hw := by decide
    g := ![![![-64118, -83217, -76759], ![-32497, 396748, 0]], ![![10977, 14317, 13296], ![6138, -68728, 0]]]
    h := ![![![-785606, 38398, -47], ![-4751043, 5977, 0]], ![![2119836, -103570, 125], ![12819953, -15876, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N2 : Ideal.span {625} * I127N2 =  Ideal.span {B.equivFun.symm ![-59, -14, 8]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E127RS2 


noncomputable def E137RS0 : RelationCertificate Table 5 ![![137, 0, 0], ![52, 1, 0]]
  ![157, 18, 5] ![![5, 0, 0], ![14, 1, 1]] where
    su := ![![685, 0, 0], ![260, 5, 0]]
    hsu := by decide
    w := ![![785, 90, 25], ![4820, 565, 155]]
    hw := by decide
    g := ![![![1, 4, -3], ![4, 0, 0]], ![![0, 2, -1], ![1, 0, 0]]]
    h := ![![![1393, 25, 0], ![-3667, 5, 0]], ![![9052, 163, 0], ![-23830, 31, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N0 : Ideal.span {5} * I137N0 =  Ideal.span {B.equivFun.symm ![157, 18, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E137RS0 


noncomputable def E137RS1 : RelationCertificate Table 5 ![![137, 0, 0], ![-29, 1, 0]]
  ![31, 3, 1] ![![5, 0, 0], ![14, 1, 1]] where
    su := ![![685, 0, 0], ![-145, 5, 0]]
    hsu := by decide
    w := ![![155, 15, 5], ![890, 115, 30]]
    hw := by decide
    g := ![![![-5, 4, -1], ![1, 0, 0]], ![![-3, -1, 0], ![1, 0, 0]]]
    h := ![![![471, -16, 0], ![2224, 1, 0]], ![![2508, -85, 0], ![11842, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N1 : Ideal.span {5} * I137N1 =  Ideal.span {B.equivFun.symm ![31, 3, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E137RS1 


noncomputable def E137RS2 : RelationCertificate Table 125 ![![137, 0, 0], ![-23, 1, 0]]
  ![-839, -99, -27] ![![125, 0, 0], ![-16, 21, 1]] where
    su := ![![17125, 0, 0], ![-2875, 125, 0]]
    hsu := by decide
    w := ![![-104875, -12375, -3375], ![-62500, -7125, -2000]]
    hw := by decide
    g := ![![![-653, 171, -128], ![196, 750, 0]], ![![119, -45, 20], ![71, -122, 0]]]
    h := ![![![-1093, 65, -1], ![-6474, 110, 0]], ![![-650, 48, -1], ![-3850, 121, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R137N2 : Ideal.span {125} * I137N2 =  Ideal.span {B.equivFun.symm ![-839, -99, -27]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E137RS2 
