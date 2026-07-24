import IdealArithmetic.Examples.NF3_3_260820_1.PrimesBelow3_3_260820_1F0
import IdealArithmetic.Examples.NF3_3_260820_1.ClassGroupData3_3_260820_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 25 ![![2, 0, 0], ![0, 1, 0]]
  ![-28, -21, -3] ![![25, 0, 0], ![-7, 1, 0]] where
    su := ![![50, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![-700, -525, -75], ![-50, -25, 0]]
    hw := by decide
    g := ![![![-27, -3629, 519], ![-115, -12978, 0]], ![![-8, -692, 99], ![-11, -2472, 0]]]
    h := ![![![-14, -9, 0], ![-3, -3, 0]], ![![-1, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {25} * I2N0 =  Ideal.span {B.equivFun.symm ![-28, -21, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 5 ![![3, 0, 0], ![-1, 1, 0]]
  ![33, 11, -2] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![15, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![165, 55, -10], ![-230, -85, 15]]
    hw := by decide
    g := ![![![-1, -4, 1], ![1, -6, 0]], ![![-3, -3, -1], ![5, 3, 0]]]
    h := ![![![24, -10, 0], ![39, -2, 0]], ![![-32, 13, -1], ![-50, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {5} * I3N0 =  Ideal.span {B.equivFun.symm ![33, 11, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 5 ![![5, 0, 0], ![1, 1, 0]]
  ![-181, -7, 4] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![25, 0, 0], ![5, 5, 0]]
    hsu := by decide
    w := ![![-905, -35, 20], ![690, 25, -15]]
    hw := by decide
    g := ![![![33, 433, -223], ![76, 1116, 0]], ![![15, 146, -74], ![28, 372, 0]]]
    h := ![![![-68, -35, -1], ![159, 9, 0]], ![![50, 24, 0], ![-112, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {5} * I5N0 =  Ideal.span {B.equivFun.symm ![-181, -7, 4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![5, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -1], ![-4, 5, 0]]]
    h := ![![![11, -5, 0], ![25, 0, 0]], ![![-2, 3, -1], ![-4, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 25 ![![7, 0, 0], ![1, 1, 0]]
  ![147, 4, -3] ![![25, 0, 0], ![-7, 1, 0]] where
    su := ![![175, 0, 0], ![25, 25, 0]]
    hsu := by decide
    w := ![![3675, 100, -75], ![-1275, -25, 25]]
    hw := by decide
    g := ![![![4, -259, 37], ![13, -924, 0]], ![![5, -63, 9], ![16, -224, 0]]]
    h := ![![![40, 19, -1], ![-133, 4, 0]], ![![-14, -7, 0], ![47, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {25} * I7N0 =  Ideal.span {B.equivFun.symm ![147, 4, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 25 ![![7, 0, 0], ![3, 1, 0]]
  ![23, 11, -2] ![![25, 0, 0], ![-7, 1, 0]] where
    su := ![![175, 0, 0], ![75, 25, 0]]
    hsu := by decide
    w := ![![575, 275, -50], ![-325, -150, 25]]
    hw := by decide
    g := ![![![-50219, -4835839, 691859], ![-179346, -17296474, 0]], ![![-17963, -1730053, 247517], ![-64152, -6187925, 0]]]
    h := ![![![920, 392, 28], ![-2139, -198, 0]], ![![-526, -227, -17], ![1223, 120, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {25} * I7N1 =  Ideal.span {B.equivFun.symm ![23, 11, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E11RS1 : RelationCertificate Table 25 ![![11, 0, 0], ![5, 1, 0]]
  ![29, 28, 4] ![![25, 0, 0], ![-7, 1, 0]] where
    su := ![![275, 0, 0], ![125, 25, 0]]
    hsu := by decide
    w := ![![725, 700, 100], ![125, 25, 0]]
    hw := by decide
    g := ![![![3212, 308969, -44204], ![11483, 1105104, 0]], ![![1498, 143930, -20592], ![5351, 514800, 0]]]
    h := ![![![1624, 445, 24], ![-3567, -260, 0]], ![![240, 68, 4], ![-527, -44, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {25} * I11N1 =  Ideal.span {B.equivFun.symm ![29, 28, 4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS1 


noncomputable def E23RS0 : RelationCertificate Table 5 ![![23, 0, 0], ![4, 1, 0]]
  ![-107, -9, 3] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![115, 0, 0], ![20, 5, 0]]
    hsu := by decide
    w := ![![-535, -45, 15], ![460, 55, -15]]
    hw := by decide
    g := ![![![13, 31, -10], ![2, 56, 0]], ![![8, 9, -2], ![4, 13, 0]]]
    h := ![![![-109, -31, -1], ![600, 26, 0]], ![![84, 21, 0], ![-460, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {5} * I23N0 =  Ideal.span {B.equivFun.symm ![-107, -9, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 5 ![![23, 0, 0], ![-8, 1, 0]]
  ![-103, -6, 2] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![115, 0, 0], ![-40, 5, 0]]
    hsu := by decide
    w := ![![-515, -30, 10], ![370, 5, -10]]
    hw := by decide
    g := ![![![27, 36, -14], ![-2, 60, 0]], ![![-14, -16, 5], ![7, -19, 0]]]
    h := ![![![-153, 27, -1], ![-427, 25, 0]], ![![134, -17, 0], ![376, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {5} * I23N1 =  Ideal.span {B.equivFun.symm ![-103, -6, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 5 ![![31, 0, 0], ![-15, 1, 0]]
  ![11, 7, 1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![155, 0, 0], ![-75, 5, 0]]
    hsu := by decide
    w := ![![55, 35, 5], ![60, 45, 5]]
    hw := by decide
    g := ![![![19, -23, 12], ![-8, -62, 0]], ![![-9, 11, -6], ![7, 31, 0]]]
    h := ![![![866, -57, 0], ![1789, 1, 0]], ![![942, -62, 0], ![1946, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {5} * I31N1 =  Ideal.span {B.equivFun.symm ![11, 7, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS1 
