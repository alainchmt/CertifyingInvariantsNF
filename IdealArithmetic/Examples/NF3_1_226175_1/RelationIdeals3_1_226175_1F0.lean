import IdealArithmetic.Examples.NF3_1_226175_1.PrimesBelow3_1_226175_1F0
import IdealArithmetic.Examples.NF3_1_226175_1.ClassGroupData3_1_226175_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 3 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![9, 0, 0], ![0, 3, 0]] where
    su := ![![9, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![9, 0, 0], ![0, 3, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {3} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 3 ![![3, 0, 0], ![1, 1, 0]]
  ![64309, 2170, 1761] ![![3, 0, 0], ![24, 2, 1]] where
    su := ![![9, 0, 0], ![3, 3, 0]]
    hsu := by decide
    w := ![![192927, 6510, 5283], ![1799556, 60723, 49278]]
    hw := by decide
    g := ![![![-14, -33, -7], ![7, 0, 0]], ![![-8, 63, -9], ![-6, 0, 0]]]
    h := ![![![35076, 16192, 2416], ![-40919, -5487, 0]], ![![327192, 151054, 22541], ![-381724, -51197, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {3} * I3N1 =  Ideal.span {B.equivFun.symm ![64309, 2170, 1761]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS1 


noncomputable def E3RS2 : RelationCertificate Table 3 ![![3, 0, 0], ![-1, 1, 0]]
  ![-1, 1, 0] ![![3, 0, 0], ![24, 1, 1]] where
    su := ![![9, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![-3, 3, 0], ![21, -12, 0]]
    hw := by decide
    g := ![![![-20, -1, -1], ![4, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![6, -5, 0], ![11, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N2 : Ideal.span {3} * I3N2 =  Ideal.span {B.equivFun.symm ![-1, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS2 


noncomputable def E11RS0 : RelationCertificate Table 3 ![![11, 0, 0], ![28, 2, 1]]
  ![-173, 133, 6] ![![3, 0, 0], ![24, 2, 1]] where
    su := ![![33, 0, 0], ![84, 6, 3]]
    hsu := by decide
    w := ![![-519, 399, 18], ![2373, -1959, 27]]
    hw := by decide
    g := ![![![430, -1061, -298], ![2711, 0, 0]], ![![1261, -3084, -866], ![7881, 0, 0]]]
    h := ![![![-3, 13, 1], ![-5, 0, 0]], ![![-7, -65, -2], ![31, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {3} * I11N0 =  Ideal.span {B.equivFun.symm ![-173, 133, 6]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![-2, 1, 0]]
  ![2, -1, 0] ![![3, 0, 0], ![24, 2, 1]] where
    su := ![![33, 0, 0], ![-6, 3, 0]]
    hsu := by decide
    w := ![![6, -3, 0], ![3, 15, 0]]
    hw := by decide
    g := ![![![-19, -2, -1], ![4, 0, 0]], ![![-1, 0, 0], ![0, 0, 0]]]
    h := ![![![14, -7, 0], ![76, 0, 0]], ![![1, 0, 0], ![5, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![2, -1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS1 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![-5, 1, 0]]
  ![-29, 26, -2] ![![3, 0, 0], ![24, 2, 1]] where
    su := ![![51, 0, 0], ![-15, 3, 0]]
    hsu := by decide
    w := ![![-87, 78, -6], ![294, -294, 45]]
    hw := by decide
    g := ![![![163, -444, -125], ![1133, 0, 0]], ![![-53, 97, 27], ![-249, 0, 0]]]
    h := ![![![-72, 20, -1], ![-239, 15, 0]], ![![284, -62, 1], ![946, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![-29, 26, -2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS1 


noncomputable def E23RS1 : RelationCertificate Table 3 ![![23, 0, 0], ![5, 1, 0]]
  ![11, -4, -4] ![![3, 0, 0], ![24, 1, 1]] where
    su := ![![69, 0, 0], ![15, 3, 0]]
    hsu := by decide
    w := ![![33, -12, -12], ![-96, 15, 51]]
    hw := by decide
    g := ![![![-139, 54, 102], ![-926, 0, 0]], ![![-53, 14, 27], ![-249, 0, 0]]]
    h := ![![![97, 20, 0], ![-444, -4, 0]], ![![-314, -71, -1], ![1438, 40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {3} * I23N1 =  Ideal.span {B.equivFun.symm ![11, -4, -4]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 9 ![![29, 0, 0], ![13, 1, 0]]
  ![2666, 90, 73] ![![9, 0, 0], ![0, 3, 0]] where
    su := ![![261, 0, 0], ![117, 9, 0]]
    hsu := by decide
    w := ![![23994, 810, 657], ![9855, 333, 270]]
    hw := by decide
    g := ![![![19, -14, 9123], ![-3, -27370, 0]], ![![8, -6, 4170], ![1, -12512, 0]]]
    h := ![![![8316, 772, 13], ![-18346, -304, 0]], ![![3420, 313, 5], ![-7545, -115, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {9} * I29N0 =  Ideal.span {B.equivFun.symm ![2666, 90, 73]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS0 


noncomputable def E29RS2 : RelationCertificate Table 9 ![![29, 0, 0], ![-3, 1, 0]]
  ![-8801, -297, -241] ![![9, 0, 0], ![0, 3, 0]] where
    su := ![![261, 0, 0], ![-27, 9, 0]]
    hsu := by decide
    w := ![![-79209, -2673, -2169], ![-32535, -1098, -891]]
    hw := by decide
    g := ![![![-34, 25, -25], ![9, 74, 0]], ![![3, -4, 3], ![1, -6, 0]]]
    h := ![![![-10615, 3462, -20], ![-99678, 339, 0]], ![![-4359, 1421, -8], ![-40932, 133, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {9} * I29N2 =  Ideal.span {B.equivFun.symm ![-8801, -297, -241]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS2 


noncomputable def E31RS0 : RelationCertificate Table 3 ![![31, 0, 0], ![8, 1, 0]]
  ![37, 1, 1] ![![3, 0, 0], ![24, 1, 1]] where
    su := ![![93, 0, 0], ![24, 3, 0]]
    hsu := by decide
    w := ![![111, 3, 3], ![978, 36, 27]]
    hw := by decide
    g := ![![![-18, 2, -1], ![2, 0, 0]], ![![-1, 1, 0], ![0, 0, 0]]]
    h := ![![![27, 3, 0], ![-100, 1, 0]], ![![314, 36, 0], ![-1176, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {3} * I31N0 =  Ideal.span {B.equivFun.symm ![37, 1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS0 


noncomputable def E31RS2 : RelationCertificate Table 3 ![![31, 0, 0], ![13, 1, 0]]
  ![-38, 37, -5] ![![3, 0, 0], ![24, 1, 1]] where
    su := ![![93, 0, 0], ![39, 3, 0]]
    hsu := by decide
    w := ![![-114, 111, -15], ![528, -495, 54]]
    hw := by decide
    g := ![![![387, -182, -341], ![3077, 0, 0]], ![![167, -84, -157], ![1414, 0, 0]]]
    h := ![![![-148, -21, -1], ![350, 26, 0]], ![![602, 46, 1], ![-1422, -13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {3} * I31N2 =  Ideal.span {B.equivFun.symm ![-38, 37, -5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS2 
