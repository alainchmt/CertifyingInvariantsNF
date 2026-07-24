import IdealArithmetic.Examples.NF3_3_806284_1.PrimesBelow3_3_806284_1F0
import IdealArithmetic.Examples.NF3_3_806284_1.ClassGroupData3_3_806284_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![0, 1, 0]]
  ![9, 6, 1] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![4, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![18, 12, 2], ![106, 62, 10]]
    hw := by decide
    g := ![![![32, 47, -1], ![-19, -7, 0]], ![![17, -2, 0], ![1, 0, 0]]]
    h := ![![![1395, 553, -13], ![277, 0, -27]], ![![8215, 3256, -77], ![1628, 0, -159]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![9, 6, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![-34, -1, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![2, 0, 0], ![-34, -1, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-34, -1, 1]]
    hw := by decide
    g := ![![![2, 13, 0], ![-6, -2, 0]], ![![17, -220, -1], ![105, 34, 0]]]
    h := ![![![2, 13, 0], ![-6, -2, 0]], ![![17, -220, -1], ![105, 34, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![-37, 1, 1]]
  ![-2911, -32, 59] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![14, 0, 0], ![-74, 2, 2]]
    hsu := by decide
    w := ![![-5822, -64, 118], ![83524, 924, -1694]]
    hw := by decide
    g := ![![![33, -1741, -3], ![819, 270, 0]], ![![11, 9318, 29], ![-4338, -1431, 0]]]
    h := ![![![7, -16, -3], ![80, 0, 0]], ![![231, 221, 34], ![-1085, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-2911, -32, 59]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![-1, 1, 0]]
  ![-5324, -59, 108] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![14, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![-10648, -118, 216], ![5800, 66, -118]]
    hw := by decide
    g := ![![![-563, -287, -83], ![-425, 0, 0]], ![![-807, -412, -119], ![-607, 0, 0]]]
    h := ![![![-745, -24, -324], ![109, 1188, 0]], ![![407, 12, 177], ![-51, -649, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![-5324, -59, 108]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0], ![-29, 1, 1]]
  ![-61, -40, -7] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![22, 0, 0], ![-58, 2, 2]]
    hsu := by decide
    w := ![![-122, -80, -14], ![-604, -404, -74]]
    hw := by decide
    g := ![![![7, -3898, -12], ![1843, 602, 0]], ![![-6, 10303, 31], ![-4868, -1591, 0]]]
    h := ![![![5, -4, -1], ![4, 0, 0]], ![![20, -20, -5], ![18, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![-61, -40, -7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![-1, 1, 0]]
  ![98, 1, -2] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![22, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![196, 2, -4], ![-108, -2, 2]]
    hw := by decide
    g := ![![![-10, -2, 1], ![-5, 0, 0]], ![![8, 1, -1], ![5, 0, 0]]]
    h := ![![![9, 0, 6], ![1, -34, 0]], ![![-4, -1, -3], ![10, 17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![98, 1, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E19RS0 : RelationCertificate Table 2 ![![19, 0, 0], ![3, 1, 0]]
  ![65, 42, 7] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![38, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![130, 84, 14], ![674, 432, 72]]
    hw := by decide
    g := ![![![32, 2, -2], ![11, 0, 0]], ![![30, 21, -1], ![-7, -3, 0]]]
    h := ![![![317, 108, 1], ![-1986, -6, 0]], ![![1645, 574, 12], ![-10306, -96, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {2} * I19N0 =  Ideal.span {B.equivFun.symm ![65, 42, 7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-6, 1, 0]]
  ![-653, -6, 13] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![38, 0, 0], ![-12, 2, 0]]
    hsu := by decide
    w := ![![-1306, -12, 26], ![18906, 232, -388]]
    hw := by decide
    g := ![![![8, 141, 31], ![-13, 0, 0]], ![![8, 18, 8], ![6, 3, 0]]]
    h := ![![![-59, -2052, 823], ![-78, -7812, 0]], ![![903, 29668, -11902], ![1284, 112972, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![-653, -6, 13]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E29RS1 : RelationCertificate Table 2 ![![29, 0, 0], ![14, 1, 0]]
  ![-543, -6, 11] ![![2, 0, 0], ![-34, -1, 1]] where
    su := ![![58, 0, 0], ![28, 2, 0]]
    hsu := by decide
    w := ![![-1086, -12, 22], ![15578, 172, -316]]
    hw := by decide
    g := ![![![27, 3, -2], ![1, 0, 0]], ![![15, -20, -1], ![10, 3, 0]]]
    h := ![![![-14291, -1255, -31], ![29564, 455, 0]], ![![204853, 17777, 416], ![-423782, -6111, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2} * I29N1 =  Ideal.span {B.equivFun.symm ![-543, -6, 11]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 
