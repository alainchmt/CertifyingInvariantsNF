import IdealArithmetic.Examples.NF3_3_405405_1.PrimesBelow3_3_405405_1F0
import IdealArithmetic.Examples.NF3_3_405405_1.ClassGroupData3_3_405405_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 4 ![![2, 0, 0], ![-31, -1, 1]]
  ![249, 357, 49] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![8, 0, 0], ![-124, -4, 4]]
    hsu := by decide
    w := ![![996, 1428, 196], ![1564, 2244, 308]]
    hw := by decide
    g := ![![![11, -31, 31], ![-7, -124, 0]], ![![-191, 428, -481], ![156, 1953, 0]]]
    h := ![![![16, 175, 28], ![-7, 0, 0]], ![![-6, 274, 45], ![-13, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {4} * I2N0 =  Ideal.span {B.equivFun.symm ![249, 357, 49]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 4 ![![5, 0, 0], ![1, 1, 0]]
  ![1031, 1479, 203] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![20, 0, 0], ![4, 4, 0]]
    hsu := by decide
    w := ![![4124, 5916, 812], ![6480, 9296, 1276]]
    hw := by decide
    g := ![![![315, 43, -26], ![-68, 75, 0]], ![![12, -1, 0], ![-3, 0, 0]]]
    h := ![![![190, 190, -49], ![81, 448, 0]], ![![300, 300, -77], ![120, 704, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {4} * I5N0 =  Ideal.span {B.equivFun.symm ![1031, 1479, 203]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 4 ![![5, 0, 0], ![-2, 1, 0]]
  ![427, 7, -9] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![20, 0, 0], ![-8, 4, 0]]
    hsu := by decide
    w := ![![1708, 28, -36], ![-760, -12, 16]]
    hw := by decide
    g := ![![![1, -3, 3], ![3, -11, 0]], ![![2, 3, -1], ![1, 4, 0]]]
    h := ![![![3951, -2135, 100], ![9664, -509, 0]], ![![-1754, 949, -45], ![-4290, 229, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {4} * I5N1 =  Ideal.span {B.equivFun.symm ![427, 7, -9]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![-3, 1, 0]]
  ![5, 7, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![14, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![10, 14, 2], ![42, 60, 8]]
    hw := by decide
    g := ![![![18, 104, 134], ![63, -270, 0]], ![![-16, -30, -40], ![-21, 81, 0]]]
    h := ![![![2, 16, -5], ![3, 36, 0]], ![![6, 65, -20], ![7, 144, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![5, 7, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![-1, 1, 0]]
  ![-49, -1, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![14, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![-98, -2, 2], ![-12, -2, 0]]
    hw := by decide
    g := ![![![30, -145, -176], ![-55, 351, 0]], ![![-5, 8, 14], ![4, -27, 0]]]
    h := ![![![-14, 7, 0], ![-49, 1, 0]], ![![0, 0, -1], ![6, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![-49, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0], ![-4, 1, 0]]
  ![25, 33, -5] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![22, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![50, 66, -10], ![-160, -182, 28]]
    hw := by decide
    g := ![![![-39, 251, 283], ![107, -559, 0]], ![![18, -67, -85], ![-23, 172, 0]]]
    h := ![![![47, -6, -1], ![123, 6, 0]], ![![-128, 27, 0], ![-332, 14, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![25, 33, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![-3, 1, 0]]
  ![3, 7, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![22, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![6, 14, 2], ![40, 58, 8]]
    hw := by decide
    g := ![![![-64, 308, 365], ![123, -731, 0]], ![![10, -57, -64], ![-22, 129, 0]]]
    h := ![![![9, -2, 0], ![32, 1, 0]], ![![34, -7, 0], ![118, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![3, 7, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 4 ![![13, 0, 0], ![4, 1, 0]]
  ![29, 37, 5] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![52, 0, 0], ![16, 4, 0]]
    hsu := by decide
    w := ![![116, 148, 20], ![156, 232, 32]]
    hw := by decide
    g := ![![![12, 2, 6], ![-1, -30, 0]], ![![0, -5, 3], ![2, -11, 0]]]
    h := ![![![269, 76, 2], ![-867, -21, 0]], ![![375, 107, 3], ![-1209, -31, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {4} * I13N0 =  Ideal.span {B.equivFun.symm ![29, 37, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 4 ![![13, 0, 0], ![5, 1, 0]]
  ![-55, -79, -11] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![52, 0, 0], ![20, 4, 0]]
    hsu := by decide
    w := ![![-220, -316, -44], ![-352, -504, -68]]
    hw := by decide
    g := ![![![-119577, -2024652, 2143721], ![-476266, -8574841, 0]], ![![-36799, -622937, 659571], ![-146533, -2638270, 0]]]
    h := ![![![-670, -165, -6], ![1731, 67, 0]], ![![-1066, -265, -10], ![2754, 113, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {4} * I13N1 =  Ideal.span {B.equivFun.symm ![-55, -79, -11]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E23RS1 : RelationCertificate Table 4 ![![23, 0, 0], ![-10, 1, 0]]
  ![7, 7, -1] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![92, 0, 0], ![-40, 4, 0]]
    hsu := by decide
    w := ![![28, 28, -4], ![-44, -48, 8]]
    hw := by decide
    g := ![![![-312, -5717, 6055], ![-1351, -24222, 0]], ![![127, 2338, -2477], ![556, 9909, 0]]]
    h := ![![![39, 6, -1], ![89, 22, 0]], ![![-47, 5, 0], ![-107, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {4} * I23N1 =  Ideal.span {B.equivFun.symm ![7, 7, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 2 ![![29, 0, 0], ![12, 1, 0]]
  ![-229, -5, 5] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![58, 0, 0], ![24, 2, 0]]
    hsu := by decide
    w := ![![-458, -10, 10], ![-44, 6, 0]]
    hw := by decide
    g := ![![![-14, -88, -65], ![-49, 115, 0]], ![![4, -122, -120], ![-59, 230, 0]]]
    h := ![![![-2585, -277, -5], ![6228, 150, 0]], ![![-254, -33, -1], ![612, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2} * I29N1 =  Ideal.span {B.equivFun.symm ![-229, -5, 5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 
