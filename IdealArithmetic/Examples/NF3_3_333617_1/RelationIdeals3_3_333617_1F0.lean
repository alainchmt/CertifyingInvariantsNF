import IdealArithmetic.Examples.NF3_3_333617_1.PrimesBelow3_3_333617_1F0
import IdealArithmetic.Examples.NF3_3_333617_1.ClassGroupData3_3_333617_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![-31, -1, 1]]
  ![1, 0, 0] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![3, 0, 0], ![-31, -1, 1]]
    hsu := by decide
    w := ![![3, 0, 0], ![-31, -1, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![1, 1, 0]]
  ![-1, -1, 0] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![9, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![-3, -3, 0], ![-24, -15, 0]]
    hw := by decide
    g := ![![![5, 0, 0], ![-1, 0, 0]], ![![6, -14, -1], ![6, 3, 0]]]
    h := ![![![0, 0, 0], ![-1, 0, 0]], ![![-3, -3, -1], ![1, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![-1, -1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![0, 1, 0]]
  ![10, 6, -1] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![15, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![30, 18, -3], ![75, 78, -12]]
    hw := by decide
    g := ![![![-8, -2, 0], ![-1, 0, 0]], ![![-14, -3, 0], ![-1, 0, 0]]]
    h := ![![![2, 1, 0], ![1, -1, 0]], ![![5, 5, 0], ![1, -4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![10, 6, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 3 ![![5, 0, 0], ![-32, 0, 1]]
  ![16, 15, 2] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![15, 0, 0], ![-96, 0, 3]]
    hsu := by decide
    w := ![![48, 45, 6], ![219, 240, 33]]
    hw := by decide
    g := ![![![29, 2, -1], ![2, 0, 0]], ![![13, 2, -1], ![5, 0, 0]]]
    h := ![![![16, 3, 0], ![2, 0, 0]], ![![21, 16, 2], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {3} * I5N1 =  Ideal.span {B.equivFun.symm ![16, 15, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![0, 1, 0]]
  ![-22, -22, -3] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![33, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![-66, -66, -9], ![-363, -354, -48]]
    hw := by decide
    g := ![![![12, 2, 0], ![-5, 0, 0]], ![![2, -1, 0], ![1, 0, 0]]]
    h := ![![![-2, -2, 0], ![0, -3, 0]], ![![-11, -11, 0], ![3, -16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![-22, -22, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![5, 1, 0]]
  ![-38, -37, -5] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![33, 0, 0], ![15, 3, 0]]
    hsu := by decide
    w := ![![-114, -111, -15], ![-582, -594, -81]]
    hw := by decide
    g := ![![![17, 11, -2], ![2, 0, 0]], ![![2, -1, 0], ![1, 0, 0]]]
    h := ![![![-248, -70, -4], ![538, 39, 0]], ![![-1264, -360, -21], ![2742, 204, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![-38, -37, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS1 : RelationCertificate Table 3 ![![13, 0, 0], ![-3, 1, 0]]
  ![-1, 6, 1] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![39, 0, 0], ![-9, 3, 0]]
    hsu := by decide
    w := ![![-3, 18, 3], ![306, 105, 9]]
    hw := by decide
    g := ![![![10, -19, 2], ![4, 0, 0]], ![![11, 14, -2], ![-1, 0, 0]]]
    h := ![![![-10, 4, 0], ![-43, 1, 0]], ![![936, -318, 4], ![4022, -49, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {3} * I13N1 =  Ideal.span {B.equivFun.symm ![-1, 6, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E23RS0 : RelationCertificate Table 3 ![![23, 0, 0], ![4, 1, 0]]
  ![4, 1, 0] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![69, 0, 0], ![12, 3, 0]]
    hsu := by decide
    w := ![![12, 3, 0], ![-69, 12, 3]]
    hw := by decide
    g := ![![![31, 2, -1], ![2, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-4, -1, 0], ![24, 0, 0]], ![![-25, -10, -1], ![138, 24, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {3} * I23N0 =  Ideal.span {B.equivFun.symm ![4, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 3 ![![23, 0, 0], ![7, 1, 0]]
  ![7, 1, 0] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![69, 0, 0], ![21, 3, 0]]
    hsu := by decide
    w := ![![21, 3, 0], ![-162, 9, 6]]
    hw := by decide
    g := ![![![11, -2, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![7, 1, 0], ![-22, 0, 0]], ![![-132, -26, -1], ![426, 25, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {3} * I23N1 =  Ideal.span {B.equivFun.symm ![7, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 
