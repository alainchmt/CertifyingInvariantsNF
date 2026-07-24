import IdealArithmetic.Examples.NF3_1_304535_3.PrimesBelow3_1_304535_3F0
import IdealArithmetic.Examples.NF3_1_304535_3.ClassGroupData3_1_304535_3

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 9 ![![3, 0, 0], ![1, 1, 0]]
  ![53, -4, -3] ![![9, 0, 0], ![3, 1, 1]] where
    su := ![![27, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![477, -36, -27], ![-576, 27, 45]]
    hw := by decide
    g := ![![![-478, -27, -16], ![-158, 0, 0]], ![![-1215, -68, -40], ![-409, 0, 0]]]
    h := ![![![28, 9, -1], ![-31, 0, 0]], ![![-36, -15, -5], ![44, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {9} * I3N1 =  Ideal.span {B.equivFun.symm ![53, -4, -3]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 1 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![3, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![4, -3, 0], ![9, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![4, -3, 0], ![9, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {1} * I3N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS2 


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0, 0], ![5, 0, 1]]
  ![-95, -8, -6] ![![3, 0, 0], ![6, 1, 1]] where
    su := ![![15, 0, 0], ![15, 0, 3]]
    hsu := by decide
    w := ![![-285, -24, -18], ![-2040, -171, -129]]
    hw := by decide
    g := ![![![-5, 1, -1], ![1, 0, 0]], ![![9, -6, -3], ![8, 0, 0]]]
    h := ![![![-1127, 40, 214], ![-1076, 104, 0]], ![![-8004, 285, 1530], ![-7693, 741, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![-95, -8, -6]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 3 ![![5, 0, 0], ![7, 0, 1]]
  ![11, 1, -2] ![![3, 0, 0], ![6, 1, 1]] where
    su := ![![15, 0, 0], ![21, 0, 3]]
    hsu := by decide
    w := ![![33, 3, -6], ![-39, -18, 18]]
    hw := by decide
    g := ![![![60, -14, -20], ![115, 0, 0]], ![![197, -43, -62], ![360, 0, 0]]]
    h := ![![![-2, 59, -1], ![3, 0, -14]], ![![-4, -354, 1], ![1, 0, 84]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {3} * I5N1 =  Ideal.span {B.equivFun.symm ![11, 1, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 3 ![![7, 0, 0], ![0, 1, 0]]
  ![42, -5, -1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![21, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![126, -15, -3], ![-147, 54, -24]]
    hw := by decide
    g := ![![![-279, -47, -46], ![80, 16, 0]], ![![-265, -44, -45], ![75, 16, 0]]]
    h := ![![![6, -1, 2], ![2, -3, 0]], ![![-7, 4, -4], ![-10, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3} * I7N0 =  Ideal.span {B.equivFun.symm ![42, -5, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![1, 1, 0]]
  ![64, -3, -5] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![33, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![192, -9, -15], ![-525, 99, -15]]
    hw := by decide
    g := ![![![949, 71, 60], ![26, 0, 0]], ![![659, 49, 40], ![19, 1, 0]]]
    h := ![![![10, 3, -5], ![-46, 10, 0]], ![![-32, -14, -5], ![177, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![64, -3, -5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![5, 1, 0]]
  ![-31, 6, -1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![33, 0, 0], ![15, 3, 0]]
    hsu := by decide
    w := ![![-93, 18, -3], ![-105, -24, 30]]
    hw := by decide
    g := ![![![274, 20, 39], ![9, -13, 0]], ![![290, 21, 30], ![10, -7, 0]]]
    h := ![![![-166, -48, -16], ![359, 35, 0]], ![![-210, -58, -15], ![455, 35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![-31, 6, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![1, 1, 0]]
  ![-1977, -166, -125] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![51, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![-5931, -498, -375], ![-11148, -936, -705]]
    hw := by decide
    g := ![![![123, 1340, -7350], ![407, 4408, 0]], ![![-10, 91, -505], ![34, 304, 0]]]
    h := ![![![-116, -116, -540], ![-5, 1811, 0]], ![![-218, -218, -1015], ![-10, 3404, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![-1977, -166, -125]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS1 
