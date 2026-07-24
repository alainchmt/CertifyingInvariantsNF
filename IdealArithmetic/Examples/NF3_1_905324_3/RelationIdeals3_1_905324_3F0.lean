import IdealArithmetic.Examples.NF3_1_905324_3.PrimesBelow3_1_905324_3F0
import IdealArithmetic.Examples.NF3_1_905324_3.ClassGroupData3_1_905324_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 3757 ![![2, 0, 0], ![0, 1, 0]]
  ![528, -91, -5] ![![3757, 0, 0], ![-1521, 1, 0]] where
    su := ![![7514, 0, 0], ![0, 3757, 0]]
    hsu := by decide
    w := ![![1983696, -341887, -18785], ![-803998, 139009, 7514]]
    hw := by decide
    g := ![![![1189, 24334, -16], ![2937, 60109, 0]], ![![240, 41064, -27], ![593, 101432, 0]]]
    h := ![![![264, -37, 0], ![-17, -5, 0]], ![![-107, 14, 0], ![9, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {3757} * I2N0 =  Ideal.span {B.equivFun.symm ![528, -91, -5]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E2RS0 


noncomputable def E7RS0 : RelationCertificate Table 221 ![![7, 0, 0], ![0, 1, 0]]
  ![-1603, -208, -43] ![![221, 0, 0], ![26, 1, 0]] where
    su := ![![1547, 0, 0], ![0, 221, 0]]
    hsu := by decide
    w := ![![-354263, -45968, -9503], ![-49504, -6409, -1326]]
    hw := by decide
    g := ![![![155, -338904, -13035], ![-1314, 2880734, 0]], ![![330, -677807, -26070], ![-2806, 5761468, 0]]]
    h := ![![![-229, -30, 0], ![2, -43, 0]], ![![-32, -5, 0], ![6, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {221} * I7N0 =  Ideal.span {B.equivFun.symm ![-1603, -208, -43]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS0 


noncomputable def E13RS0 : RelationCertificate Table 1 ![![13, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![13, 0, 0], ![0, 1, 0]] where
    su := ![![13, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![13, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {1} * I13N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 169 ![![13, 0, 0], ![5, 1, 0]]
  ![-801, -104, -21] ![![169, 0, 0], ![-13, 1, 0]] where
    su := ![![2197, 0, 0], ![845, 169, 0]]
    hsu := by decide
    w := ![![-135369, -17576, -3549], ![6591, 845, 169]]
    hw := by decide
    g := ![![![-7228, -15991407, 1230151], ![-93959, -207895520, 0]], ![![-3678, -8138484, 626059], ![-47811, -105803970, 0]]]
    h := ![![![-402807, -97874, -3465], ![1047138, 45024, 0]], ![![19603, 4760, 168], ![-50960, -2183, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {169} * I13N1 =  Ideal.span {B.equivFun.symm ![-801, -104, -21]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 1 ![![17, 0, 0], ![-8, 1, 0]]
  ![1, 0, 0] ![![17, 0, 0], ![-8, 1, 0]] where
    su := ![![17, 0, 0], ![-8, 1, 0]]
    hsu := by decide
    w := ![![17, 0, 0], ![-8, 1, 0]]
    hw := by decide
    g := ![![![137, -17, 0], ![289, 0, 0]], ![![-56, 15, -1], ![-118, 17, 0]]]
    h := ![![![137, -17, 0], ![289, 0, 0]], ![![-56, 15, -1], ![-118, 17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {1} * I17N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS1 


noncomputable def E29RS1 : RelationCertificate Table 13 ![![29, 0, 0], ![5, 1, 0]]
  ![-25, 0, 1] ![![13, 0, 0], ![0, 1, 0]] where
    su := ![![377, 0, 0], ![65, 13, 0]]
    hsu := by decide
    w := ![![-325, 0, 13], ![182, -39, 0]]
    hw := by decide
    g := ![![![-9, -2, 45], ![12, -588, 0]], ![![-3, -1, 8], ![8, -105, 0]]]
    h := ![![![-25, -5, 0], ![140, 1, 0]], ![![6, 1, 0], ![-32, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {13} * I29N1 =  Ideal.span {B.equivFun.symm ![-25, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E29RS1 


noncomputable def E31RS0 : RelationCertificate Table 2873 ![![31, 0, 0], ![8, 1, 0]]
  ![-1481, 182, 27] ![![2873, 0, 0], ![-858, 1, 0]] where
    su := ![![89063, 0, 0], ![22984, 2873, 0]]
    hsu := by decide
    w := ![![-4254913, 522886, 77571], ![1275612, -158015, -22984]]
    hw := by decide
    g := ![![![497934045, 5217445146016, -6080939075], ![1667324604, 17470537962504, 0]], ![![137404928, 1439751072778, -1678031740], ![460098319, 4820985189032, 0]]]
    h := ![![![-1479, -188, -1], ![5546, 58, 0]], ![![436, 53, 0], ![-1634, -8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {2873} * I31N0 =  Ideal.span {B.equivFun.symm ![-1481, 182, 27]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 2873 ![![31, 0, 0], ![-4, 1, 0]]
  ![-3611, -468, -101] ![![2873, 0, 0], ![-858, 1, 0]] where
    su := ![![89063, 0, 0], ![-11492, 2873, 0]]
    hsu := by decide
    w := ![![-10374403, -1344564, -290173], ![3079856, 399347, 86190]]
    hw := by decide
    g := ![![![239, -3697122, 4309], ![800, -12379756, 0]], ![![350, 397253, -463], ![1172, 1330197, 0]]]
    h := ![![![-4533, 1108, -8], ![-34228, 147, 0]], ![![1352, -329, 2], ![10210, -32, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {2873} * I31N1 =  Ideal.span {B.equivFun.symm ![-3611, -468, -101]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E31RS1 
