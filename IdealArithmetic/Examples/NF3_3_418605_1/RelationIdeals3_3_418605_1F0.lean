import IdealArithmetic.Examples.NF3_3_418605_1.PrimesBelow3_3_418605_1F0
import IdealArithmetic.Examples.NF3_3_418605_1.ClassGroupData3_3_418605_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![-24, 0, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![2, 0, 0], ![-24, 0, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-24, 0, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![38, 9, -3] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![76, 18, -6], ![-372, 0, 8]]
    hw := by decide
    g := ![![![4, 36, 13], ![-5, 0, 0]], ![![20, 221, 80], ![-31, 0, 0]]]
    h := ![![![6, -4, 12], ![17, -9, 0]], ![![0, 66, -79], ![-132, 54, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![38, 9, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 2 ![![5, 0, 0], ![1, 1, 0]]
  ![-47, -30, -9] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![10, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-94, -60, -18], ![-1356, -684, -194]]
    hw := by decide
    g := ![![![11, 168, -33], ![-33, 0, 0]], ![![7, -275, 53], ![56, 0, 0]]]
    h := ![![![-6, -6, -12], ![0, 17, 0]], ![![-64, -64, -221], ![-22, 336, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2} * I5N0 =  Ideal.span {B.equivFun.symm ![-47, -30, -9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![-27, 2, 1]]
  ![-9903, -5582, -1629] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![14, 0, 0], ![-54, 4, 2]]
    hsu := by decide
    w := ![![-19806, -11164, -3258], ![-222876, -125628, -36662]]
    hw := by decide
    g := ![![![5, -52, -25], ![155, 0, 0]], ![![65, 228, 103], ![-660, 0, 0]]]
    h := ![![![-138, -892, -280], ![331, 0, 0]], ![![-1791, -10020, -3142], ![3663, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-9903, -5582, -1629]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![0, 1, 0]]
  ![39, 16, -5] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![14, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![78, 32, -10], ![36, 12, -10]]
    hw := by decide
    g := ![![![23, 50, 21], ![-139, 0, 0]], ![![10, -15, -7], ![43, 0, 0]]]
    h := ![![![0, -4, 16], ![5, -39, 0]], ![![0, -2, 7], ![2, -18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![39, 16, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![5, 1, 0]]
  ![34, 1, -1] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![22, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![68, 2, -2], ![-780, -24, 22]]
    hw := by decide
    g := ![![![15, 1, -1], ![1, 0, 0]], ![![22, -1, -1], ![2, 0, 0]]]
    h := ![![![134, -556, -416], ![17, 1525, 0]], ![![-1570, 6370, 4771], ![-122, -17490, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![34, 1, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS1 : RelationCertificate Table 2 ![![13, 0, 0], ![-4, 1, 0]]
  ![-9, -1, 0] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![26, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![-18, -2, 0], ![144, -12, -10]]
    hw := by decide
    g := ![![![22, -5, 0], ![3, 0, 0]], ![![1, 5, -1], ![-1, 0, 0]]]
    h := ![![![-41, -200, 120], ![-1, -520, 0]], ![![356, 1705, -1025], ![29, 4440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {2} * I13N1 =  Ideal.span {B.equivFun.symm ![-9, -1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![-9, 1, 0]]
  ![-2693, -1518, -443] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![46, 0, 0], ![-18, 2, 0]]
    hsu := by decide
    w := ![![-5386, -3036, -886], ![-60612, -34164, -9970]]
    hw := by decide
    g := ![![![23, -96, 24], ![-5, 0, 0]], ![![-9, 79, -18], ![-4, 0, 0]]]
    h := ![![![-19596, -192228, 57638], ![-664, -442039, 0]], ![![-220617, -2163267, 648641], ![-7701, -4974576, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![-2693, -1518, -443]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E31RS0 : RelationCertificate Table 2 ![![31, 0, 0], ![0, 1, 0]]
  ![-8023, -237, 230] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![62, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![-16046, -474, 460], ![183768, 5436, -5270]]
    hw := by decide
    g := ![![![-4, -645, -236], ![95, 0, 0]], ![![3, -235, -86], ![35, 0, 0]]]
    h := ![![![0, 250, -769], ![36, 8023, 0]], ![![0, -2874, 8807], ![-72, -91884, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {2} * I31N0 =  Ideal.span {B.equivFun.symm ![-8023, -237, 230]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS0 
