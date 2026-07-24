import IdealArithmetic.Examples.NF3_1_356631_2.PrimesBelow3_1_356631_2F2
import IdealArithmetic.Examples.NF3_1_356631_2.ClassGroupData3_1_356631_2

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 3 ![![83, 0, 0], ![-23, 1, 0]]
  ![-48, -17, 5] ![![3, 0, 0], ![-25, -3, 1]] where
    su := ![![249, 0, 0], ![-69, 3, 0]]
    hsu := by decide
    w := ![![-144, -51, 15], ![-4848, -300, 165]]
    hw := by decide
    g := ![![![10, 144, 97], ![-109, 0, 0]], ![![17, -16, -13], ![16, 0, 0]]]
    h := ![![![-3368, 162, -2], ![-12152, 57, 0]], ![![-114938, 5330, -43], ![-414706, 1208, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {3} * I83N1 =  Ideal.span {B.equivFun.symm ![-48, -17, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E83RS1 


noncomputable def E89RS0 : RelationCertificate Table 3 ![![89, 0, 0], ![33, 1, 0]]
  ![1527, 421, 101] ![![3, 0, 0], ![-25, -3, 1]] where
    su := ![![267, 0, 0], ![99, 3, 0]]
    hsu := by decide
    w := ![![4581, 1263, 303], ![-15873, -4377, -1050]]
    hw := by decide
    g := ![![![17, -45, 12], ![23, 0, 0]], ![![2, -16, 4], ![3, 0, 0]]]
    h := ![![![12252, 407, 4], ![-32997, -85, 0]], ![![-42658, -1506, -22], ![114887, 536, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N0 : Ideal.span {3} * I89N0 =  Ideal.span {B.equivFun.symm ![1527, 421, 101]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E89RS0 


noncomputable def E89RS2 : RelationCertificate Table 3 ![![89, 0, 0], ![-14, 1, 0]]
  ![-219, -20, 9] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![267, 0, 0], ![-42, 3, 0]]
    hsu := by decide
    w := ![![-657, -60, 27], ![-1707, 99, 9]]
    hw := by decide
    g := ![![![-467124, 1255501, -191010], ![2992172, 0, -201600]], ![![72313, -194310, 29556], ![-463067, 0, 31200]]]
    h := ![![![-9099, 678, -6], ![-57828, 181, 0]], ![![-23645, 1731, -9], ![-150274, 268, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {3} * I89N2 =  Ideal.span {B.equivFun.symm ![-219, -20, 9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS2 


noncomputable def E97RS1 : RelationCertificate Table 3 ![![97, 0, 0], ![-3, 1, 0]]
  ![-3, 1, 0] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![291, 0, 0], ![-9, 3, 0]]
    hsu := by decide
    w := ![![-9, 3, 0], ![264, 18, -9]]
    hw := by decide
    g := ![![![-282, 806, -123], ![1918, 0, -129]], ![![29, -17, 2], ![-42, 0, 3]]]
    h := ![![![-24, 11, -3], ![-775, 97, 0]], ![![724, -241, 0], ![23380, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {3} * I97N1 =  Ideal.span {B.equivFun.symm ![-3, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS1 


noncomputable def E101RS0 : RelationCertificate Table 3 ![![101, 0, 0], ![42, 1, 0]]
  ![258, 71, 17] ![![3, 0, 0], ![-25, -3, 1]] where
    su := ![![303, 0, 0], ![126, 3, 0]]
    hsu := by decide
    w := ![![774, 213, 51], ![-2670, -738, -177]]
    hw := by decide
    g := ![![![15, 1, 2], ![38, 0, 0]], ![![2, -1, 1], ![12, 0, 0]]]
    h := ![![![11706, 375, 7], ![-28144, -230, 0]], ![![-40654, -1354, -28], ![97742, 923, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {3} * I101N0 =  Ideal.span {B.equivFun.symm ![258, 71, 17]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 3 ![![101, 0, 0], ![-21, 1, 0]]
  ![-96, -9, 4] ![![3, 0, 0], ![-25, -3, 1]] where
    su := ![![303, 0, 0], ![-63, 3, 0]]
    hsu := by decide
    w := ![![-288, -27, 12], ![-1569, -12, 33]]
    hw := by decide
    g := ![![![11, -26, -19], ![22, 0, 0]], ![![14, 4, 1], ![0, 0, 0]]]
    h := ![![![-6066, 317, -4], ![-29170, 136, 0]], ![![-33212, 1659, -11], ![-159709, 374, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {3} * I101N1 =  Ideal.span {B.equivFun.symm ![-96, -9, 4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS1 


noncomputable def E107RS0 : RelationCertificate Table 3 ![![107, 0, 0], ![12, 1, 0]]
  ![12, 1, 0] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![321, 0, 0], ![36, 3, 0]]
    hsu := by decide
    w := ![![36, 3, 0], ![-111, -12, 6]]
    hw := by decide
    g := ![![![679, -1820, 277], ![-4334, 0, 292]], ![![84, -205, 31], ![-489, 0, 33]]]
    h := ![![![-12, -1, 0], ![108, 0, 0]], ![![-59, -13, -2], ![523, 72, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N0 : Ideal.span {3} * I107N0 =  Ideal.span {B.equivFun.symm ![12, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS0 


noncomputable def E107RS1 : RelationCertificate Table 3 ![![107, 0, 0], ![-24, 1, 0]]
  ![6303, 1738, 417] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![321, 0, 0], ![-72, 3, 0]]
    hsu := by decide
    w := ![![18909, 5214, 1251], ![13281, 3663, 879]]
    hw := by decide
    g := ![![![-162682, 437311, -66512], ![1042144, 0, -70226]], ![![33436, -89852, 13665], ![-214128, 0, 14430]]]
    h := ![![![459405, -19884, 99], ![2047918, -3392, 0]], ![![322657, -13969, 70], ![1438328, -2399, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {3} * I107N1 =  Ideal.span {B.equivFun.symm ![6303, 1738, 417]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS1 


noncomputable def E109RS1 : RelationCertificate Table 3 ![![109, 0, 0], ![-23, 1, 0]]
  ![-732, -79, 33] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![327, 0, 0], ![-69, 3, 0]]
    hsu := by decide
    w := ![![-2196, -237, 99], ![-9105, 153, 138]]
    hw := by decide
    g := ![![![-15883, 43575, -6038], ![101296, 0, -6860]], ![![-2265, 6022, -973], ![14596, 0, -980]]]
    h := ![![![-3880, 193, -3], ![-18356, 120, 0]], ![![-16242, 747, -5], ![-76841, 197, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {3} * I109N1 =  Ideal.span {B.equivFun.symm ![-732, -79, 33]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 3 ![![113, 0, 0], ![-6, 1, 0]]
  ![-6, 1, 0] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![339, 0, 0], ![-18, 3, 0]]
    hsu := by decide
    w := ![![-18, 3, 0], ![339, 24, -12]]
    hw := by decide
    g := ![![![-376660, 1012420, -153996], ![2412709, 0, -162560]], ![![14147, -37964, 5774], ![-90474, 0, 6096]]]
    h := ![![![-6, 7, -3], ![-112, 113, 0]], ![![127, -17, -2], ![2373, 74, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {3} * I113N1 =  Ideal.span {B.equivFun.symm ![-6, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E113RS1 


noncomputable def E127RS1 : RelationCertificate Table 3 ![![127, 0, 0], ![-15, 1, 0]]
  ![-15, 1, 0] ![![3, 0, 0], ![-25, -2, 1]] where
    su := ![![381, 0, 0], ![-45, 3, 0]]
    hsu := by decide
    w := ![![-45, 3, 0], ![564, 42, -21]]
    hw := by decide
    g := ![![![-43, 137, -22], ![329, 0, -22]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-30, 17, -3], ![-253, 127, 0]], ![![464, -26, -1], ![3916, 40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {3} * I127N1 =  Ideal.span {B.equivFun.symm ![-15, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 3 ![![131, 0, 0], ![38, 1, 0]]
  ![-39, -1, 1] ![![3, 0, 0], ![-25, -3, 1]] where
    su := ![![393, 0, 0], ![114, 3, 0]]
    hsu := by decide
    w := ![![-117, -3, 3], ![219, 57, -18]]
    hw := by decide
    g := ![![![19, 7, 2], ![-1, 0, 0]], ![![2, 2, 1], ![-1, 0, 0]]]
    h := ![![![-2441, -77, -1], ![8414, 44, 0]], ![![4495, 119, 0], ![-15494, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {3} * I131N1 =  Ideal.span {B.equivFun.symm ![-39, -1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E131RS1 
