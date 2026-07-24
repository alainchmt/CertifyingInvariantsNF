import IdealArithmetic.Examples.NF3_1_532652_1.PrimesBelow3_1_532652_1F0
import IdealArithmetic.Examples.NF3_1_532652_1.ClassGroupData3_1_532652_1

set_option linter.all false

noncomputable section


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![-43, -4, 1]]
  ![1, 0, 0] ![![5, 0, 0], ![-43, -4, 1]] where
    su := ![![5, 0, 0], ![-43, -4, 1]]
    hsu := by decide
    w := ![![5, 0, 0], ![-43, -4, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![-1, 1, 0]]
  ![169, 20, -4] ![![5, 0, 0], ![-43, -4, 1]] where
    su := ![![25, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![845, 100, -20], ![1445, -200, 5]]
    hw := by decide
    g := ![![![25, 76, 16], ![-28, 0, 0]], ![![3, 125, 28], ![-52, 0, 0]]]
    h := ![![![76, -39, 0], ![211, -4, 0]], ![![130, -82, 2], ![361, -9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![169, 20, -4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 1 ![![7, 0, 0], ![-41, -3, 1]]
  ![1, 0, 0] ![![7, 0, 0], ![-41, -3, 1]] where
    su := ![![7, 0, 0], ![-41, -3, 1]]
    hsu := by decide
    w := ![![7, 0, 0], ![-41, -3, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {1} * I7N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 7 ![![7, 0, 0], ![3, 1, 0]]
  ![-75969, -28118, -2971] ![![7, 0, 0], ![-41, -3, 1]] where
    su := ![![49, 0, 0], ![21, 7, 0]]
    hsu := by decide
    w := ![![-531783, -196826, -20797], ![-1532881, -567357, -59948]]
    hw := by decide
    g := ![![![81, 16, 5], ![-236, 0, 0]], ![![21, 25, -5], ![66, 0, 0]]]
    h := ![![![-816882, -349870, -26150], ![1880735, 180079, 0]], ![![-2354680, -1008502, -75376], ![5421259, 519068, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {7} * I7N1 =  Ideal.span {B.equivFun.symm ![-75969, -28118, -2971]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 35 ![![11, 0, 0], ![0, 1, 0]]
  ![11, -1, 0] ![![35, 0, 0], ![-48, 11, 1]] where
    su := ![![385, 0, 0], ![0, 35, 0]]
    hsu := by decide
    w := ![![385, -35, 0], ![-770, 105, 0]]
    hw := by decide
    g := ![![![3, 0, 0], ![1, 0, 0]], ![![2, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![-1, 0, 0]], ![![-2, 0, 0], ![3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {35} * I11N0 =  Ideal.span {B.equivFun.symm ![11, -1, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 7 ![![11, 0, 0], ![3, 1, 0]]
  ![3, 1, 0] ![![7, 0, 0], ![-41, -3, 1]] where
    su := ![![77, 0, 0], ![21, 7, 0]]
    hsu := by decide
    w := ![![21, 7, 0], ![119, 14, 0]]
    hw := by decide
    g := ![![![39, 3, -1], ![8, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-3, -1, 0], ![12, 0, 0]], ![![13, 4, 0], ![-42, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {7} * I11N1 =  Ideal.span {B.equivFun.symm ![3, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 5 ![![11, 0, 0], ![-3, 1, 0]]
  ![-103, -38, -4] ![![5, 0, 0], ![-43, -4, 1]] where
    su := ![![55, 0, 0], ![-15, 5, 0]]
    hsu := by decide
    w := ![![-515, -190, -20], ![-895, -330, -35]]
    hw := by decide
    g := ![![![38, 6, -1], ![-3, 0, 0]], ![![42, 3, -1], ![11, 0, 0]]]
    h := ![![![-149, 48, -2], ![-512, 18, 0]], ![![-265, 84, -3], ![-912, 26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {5} * I11N2 =  Ideal.span {B.equivFun.symm ![-103, -38, -4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS2 


noncomputable def E19RS1 : RelationCertificate Table 35 ![![19, 0, 0], ![-5, 1, 0]]
  ![-25, -9, -1] ![![35, 0, 0], ![-48, 11, 1]] where
    su := ![![665, 0, 0], ![-175, 35, 0]]
    hsu := by decide
    w := ![![-875, -315, -35], ![-3640, -1365, -140]]
    hw := by decide
    g := ![![![-5, -3, 0], ![8, 0, 0]], ![![3, 1, 0], ![-3, 0, 0]]]
    h := ![![![-35, 11, -1], ![-128, 18, 0]], ![![-146, 30, -1], ![-534, 15, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {35} * I19N1 =  Ideal.span {B.equivFun.symm ![-25, -9, -1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 35 ![![23, 0, 0], ![-5, 1, 0]]
  ![-13, -2, 0] ![![35, 0, 0], ![-48, 11, 1]] where
    su := ![![805, 0, 0], ![-175, 35, 0]]
    hsu := by decide
    w := ![![-455, -70, 0], ![140, -175, -35]]
    hw := by decide
    g := ![![![45, -9, -1], ![31, 0, 0]], ![![1, -1, 0], ![2, 0, 0]]]
    h := ![![![-2601, 545, -5], ![-11962, 115, 0]], ![![828, -171, 1], ![3808, -24, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {35} * I23N1 =  Ideal.span {B.equivFun.symm ![-13, -2, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 7 ![![31, 0, 0], ![-4, 1, 0]]
  ![73, 68, -8] ![![7, 0, 0], ![-41, -3, 1]] where
    su := ![![217, 0, 0], ![-28, 7, 0]]
    hsu := by decide
    w := ![![511, 476, -56], ![19271, 945, -315]]
    hw := by decide
    g := ![![![38, 1209, 257], ![-687, 0, 0]], ![![19, 214, 45], ![-119, 0, 0]]]
    h := ![![![95, -18, -1], ![718, 23, 0]], ![![3463, -849, 1], ![26150, -76, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {7} * I31N1 =  Ideal.span {B.equivFun.symm ![73, 68, -8]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS1 
