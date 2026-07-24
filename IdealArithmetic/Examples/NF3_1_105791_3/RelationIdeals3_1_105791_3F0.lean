import IdealArithmetic.Examples.NF3_1_105791_3.PrimesBelow3_1_105791_3F0
import IdealArithmetic.Examples.NF3_1_105791_3.ClassGroupData3_1_105791_3

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0], ![0, 1, 0]]
  ![9, -2, 0] ![![9, 0, 0], ![-7, 0, 1]] where
    su := ![![27, 0, 0], ![0, 9, 0]]
    hsu := by decide
    w := ![![81, -18, 0], ![-189, 0, 9]]
    hw := by decide
    g := ![![![-2, -2, -1], ![5, 0, 0]], ![![0, -3, -2], ![12, 0, 0]]]
    h := ![![![3, -1, 0], ![1, 0, 0]], ![![-7, 0, 0], ![0, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![9, -2, 0]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 1 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![3, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![2, 1, -2], ![3, 6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![2, 1, -2], ![3, 6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {1} * I3N2 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS2 


noncomputable def E7RS0 : RelationCertificate Table 9 ![![7, 0, 0], ![0, 1, 0]]
  ![0, 1, 0] ![![9, 0, 0], ![-7, 0, 1]] where
    su := ![![63, 0, 0], ![0, 9, 0]]
    hsu := by decide
    w := ![![0, 9, 0], ![63, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {9} * I7N0 =  Ideal.span {B.equivFun.symm ![0, 1, 0]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E7RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![4, 1, 0]]
  ![15, 5, 1] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![33, 0, 0], ![12, 3, 0]]
    hsu := by decide
    w := ![![45, 15, 3], ![78, 27, 6]]
    hw := by decide
    g := ![![![-40, 384, 425], ![118, -1274, 0]], ![![-17, 177, 196], ![56, -588, 0]]]
    h := ![![![9, 2, 0], ![-21, 1, 0]], ![![22, 5, 0], ![-54, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![15, 5, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E17RS0 : RelationCertificate Table 3 ![![17, 0, 0], ![5, 1, 0]]
  ![12, 4, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![51, 0, 0], ![15, 3, 0]]
    hsu := by decide
    w := ![![36, 12, 3], ![51, 15, 3]]
    hw := by decide
    g := ![![![0, -5, 6], ![1, -19, 0]], ![![-1, -2, 2], ![1, -6, 0]]]
    h := ![![![16, 3, 0], ![-52, 1, 0]], ![![26, 5, 0], ![-85, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {3} * I17N0 =  Ideal.span {B.equivFun.symm ![12, 4, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![7, 1, 0]]
  ![-12, -2, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![51, 0, 0], ![21, 3, 0]]
    hsu := by decide
    w := ![![-36, -6, 3], ![75, -3, -3]]
    hw := by decide
    g := ![![![29, 409, -457], ![128, 1368, 0]], ![![15, 226, -254], ![73, 760, 0]]]
    h := ![![![-32, -12, -1], ![76, 18, 0]], ![![34, 5, 0], ![-79, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![-12, -2, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 9 ![![19, 0, 0], ![1, 1, 0]]
  ![-27, -10, -2] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![171, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![-243, -90, -18], ![-234, -81, -18]]
    hw := by decide
    g := ![![![3, -67, -17], ![1, 151, 0]], ![![-1, -4, -1], ![1, 9, 0]]]
    h := ![![![-2, -2, -1], ![11, 17, 0]], ![![-2, -2, -1], ![12, 17, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {9} * I19N0 =  Ideal.span {B.equivFun.symm ![-27, -10, -2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 9 ![![19, 0, 0], ![2, 1, 0]]
  ![27, 8, 2] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![171, 0, 0], ![18, 9, 0]]
    hsu := by decide
    w := ![![243, 72, 18], ![18, 9, 0]]
    hw := by decide
    g := ![![![1, -96, 24], ![-4, -218, 0]], ![![0, -16, 4], ![1, -36, 0]]]
    h := ![![![409, 206, 1], ![-3872, -17, 0]], ![![30, 15, 0], ![-284, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {9} * I19N1 =  Ideal.span {B.equivFun.symm ![27, 8, 2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 3 ![![19, 0, 0], ![-3, 1, 0]]
  ![-3, 1, 0] ![![3, 0, 0], ![-4, 0, 1]] where
    su := ![![57, 0, 0], ![-9, 3, 0]]
    hsu := by decide
    w := ![![-9, 3, 0], ![75, 3, -3]]
    hw := by decide
    g := ![![![2, 1, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-24, 11, -1], ![-151, 19, 0]], ![![226, -75, 0], ![1423, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {3} * I19N2 =  Ideal.span {B.equivFun.symm ![-3, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS2 


noncomputable def E23RS0 : RelationCertificate Table 3 ![![23, 0, 0], ![3, 1, 0]]
  ![3, 1, 0] ![![3, 0, 0], ![-4, 0, 1]] where
    su := ![![69, 0, 0], ![9, 3, 0]]
    hsu := by decide
    w := ![![9, 3, 0], ![51, 3, 3]]
    hw := by decide
    g := ![![![2, -1, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-3, -1, 0], ![24, 0, 0]], ![![13, 4, 0], ![-94, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {3} * I23N0 =  Ideal.span {B.equivFun.symm ![3, 1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 9 ![![23, 0, 0], ![-2, 1, 0]]
  ![9, 5, 1] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![207, 0, 0], ![-18, 9, 0]]
    hsu := by decide
    w := ![![81, 45, 9], ![99, 36, 9]]
    hw := by decide
    g := ![![![-3686, 89283, 22551], ![8287, -202958, 0]], ![![301, -7373, -1862], ![-676, 16758, 0]]]
    h := ![![![167, -83, 0], ![1916, 1, 0]], ![![205, -102, 0], ![2352, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {9} * I23N1 =  Ideal.span {B.equivFun.symm ![9, 5, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 9 ![![23, 0, 0], ![-1, 1, 0]]
  ![18, 4, 1] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![207, 0, 0], ![-9, 9, 0]]
    hsu := by decide
    w := ![![162, 36, 9], ![-9, 9, 0]]
    hw := by decide
    g := ![![![-7, 6, -1], ![-23, 8, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![2, -1, 0], ![28, 1, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {9} * I23N2 =  Ideal.span {B.equivFun.symm ![18, 4, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E23RS2 


noncomputable def E31RS1 : RelationCertificate Table 3 ![![31, 0, 0], ![-12, 1, 0]]
  ![-3, -4, 1] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![93, 0, 0], ![-36, 3, 0]]
    hsu := by decide
    w := ![![-9, -12, 3], ![60, 0, -3]]
    hw := by decide
    g := ![![![650, -6659, -7322], ![-2002, 21962, 0]], ![![-233, 2359, 2595], ![711, -7784, 0]]]
    h := ![![![-9, 1, 0], ![-23, 1, 0]], ![![164, -14, 0], ![422, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {3} * I31N1 =  Ideal.span {B.equivFun.symm ![-3, -4, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS1 
