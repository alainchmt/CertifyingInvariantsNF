import IdealArithmetic.Examples.NF3_1_64823_1.PrimesBelow3_1_64823_1F0
import IdealArithmetic.Examples.NF3_1_64823_1.ClassGroupData3_1_64823_1

set_option linter.all false

noncomputable section


noncomputable def E5RS0 : RelationCertificate Table 11 ![![5, 0, 0], ![-2, -2, 1]]
  ![3, -2, 1] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![55, 0, 0], ![-22, -22, 11]]
    hsu := by decide
    w := ![![33, -22, 11], ![55, 0, 0]]
    hw := by decide
    g := ![![![38, -2393, -1206], ![-208, 13266, 0]], ![![-19, 1196, 603], ![109, -6633, 0]]]
    h := ![![![1, 0, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {11} * I5N0 =  Ideal.span {B.equivFun.symm ![3, -2, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 11 ![![5, 0, 0], ![2, 1, 0]]
  ![-8, -2, 1] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![55, 0, 0], ![22, 11, 0]]
    hsu := by decide
    w := ![![-88, -22, 11], ![33, -11, 0]]
    hw := by decide
    g := ![![![-91, 5537, 2791], ![494, -30702, 0]], ![![-53, 3148, 1587], ![284, -17458, 0]]]
    h := ![![![-112, -68, -6], ![276, 31, 0]], ![![33, 20, 2], ![-81, -10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {11} * I5N1 =  Ideal.span {B.equivFun.symm ![-8, -2, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 11 ![![7, 0, 0], ![0, 1, 0]]
  ![28, 7, 2] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![77, 0, 0], ![0, 11, 0]]
    hsu := by decide
    w := ![![308, 77, 22], ![154, 44, 11]]
    hw := by decide
    g := ![![![1, 2, 1], ![2, -12, 0]], ![![-1, 0, 0], ![2, 0, 0]]]
    h := ![![![4, 0, 0], ![7, 2, 0]], ![![2, 0, 0], ![4, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {11} * I7N0 =  Ideal.span {B.equivFun.symm ![28, 7, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![7, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![7, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 77 ![![7, 0, 0], ![-1, 1, 0]]
  ![70, 23, 5] ![![77, 0, 0], ![-20, 1, 0]] where
    su := ![![539, 0, 0], ![-77, 77, 0]]
    hsu := by decide
    w := ![![5390, 1771, 385], ![-1155, -385, -77]]
    hw := by decide
    g := ![![![9, 280, -14], ![35, 1080, 0]], ![![15, 59, -3], ![57, 230, 0]]]
    h := ![![![22, -8, 0], ![84, 5, 0]], ![![-4, 2, -1], ![-13, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {77} * I7N2 =  Ideal.span {B.equivFun.symm ![70, 23, 5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS2 


noncomputable def E11RS0 : RelationCertificate Table 1 ![![11, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![2, 1, 0]] where
    su := ![![11, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![9, 4, 0], ![-44, 0, 0]], ![![-2, -1, 0], ![12, 0, 0]]]
    h := ![![![9, 4, 0], ![-44, 0, 0]], ![![-2, -1, 0], ![12, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {1} * I11N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS0 


noncomputable def E13RS1 : RelationCertificate Table 7 ![![13, 0, 0], ![5, 1, 0]]
  ![21, 2, -2] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![91, 0, 0], ![35, 7, 0]]
    hsu := by decide
    w := ![![147, 14, -14], ![-77, 21, 0]]
    hw := by decide
    g := ![![![100, 93, 2], ![-621, -8, 0]], ![![50, 45, 1], ![-297, -3, 0]]]
    h := ![![![407, 97, 3], ![-1054, -41, 0]], ![![-217, -53, -2], ![562, 26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {7} * I13N1 =  Ideal.span {B.equivFun.symm ![21, 2, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS1 


noncomputable def E23RS1 : RelationCertificate Table 7 ![![23, 0, 0], ![-6, 1, 0]]
  ![-7, -1, 1] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![161, 0, 0], ![-42, 7, 0]]
    hsu := by decide
    w := ![![-49, -7, 7], ![42, -7, 0]]
    hw := by decide
    g := ![![![-466, -464, 3], ![3274, -20, 0]], ![![91, 90, -1], ![-638, 7, 0]]]
    h := ![![![-5, 1, 0], ![-18, 1, 0]], ![![18, -3, 0], ![68, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {7} * I23N1 =  Ideal.span {B.equivFun.symm ![-7, -1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 7 ![![29, 0, 0], ![13, 1, 0]]
  ![-42, -11, -3] ![![7, 0, 0], ![1, 1, 0]] where
    su := ![![203, 0, 0], ![91, 7, 0]]
    hsu := by decide
    w := ![![-294, -77, -21], ![-189, -56, -14]]
    hw := by decide
    g := ![![![594, -29988, -30588], ![-4199, 214118, 0]], ![![283, -14300, -14585], ![-1996, 102096, 0]]]
    h := ![![![-144, -23, -1], ![318, 26, 0]], ![![-100, -20, -1], ![221, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {7} * I29N1 =  Ideal.span {B.equivFun.symm ![-42, -11, -3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 77 ![![31, 0, 0], ![-11, 1, 0]]
  ![-21, 3, 4] ![![77, 0, 0], ![-20, 1, 0]] where
    su := ![![2387, 0, 0], ![-847, 77, 0]]
    hsu := by decide
    w := ![![-1617, 231, 308], ![616, -77, -77]]
    hw := by decide
    g := ![![![8, 620, -31], ![31, 2388, 0]], ![![19, -181, 9], ![73, -693, 0]]]
    h := ![![![-22754, 2257, -17], ![-64123, 531, 0]], ![![8686, -856, 6], ![24478, -187, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {77} * I31N1 =  Ideal.span {B.equivFun.symm ![-21, 3, 4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E31RS1 
