import IdealArithmetic.Examples.NF3_1_662796_2.PrimesBelow3_1_662796_2F0
import IdealArithmetic.Examples.NF3_1_662796_2.ClassGroupData3_1_662796_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 833 ![![2, 0, 0], ![0, 1, 0]]
  ![442, 115, 20] ![![833, 0, 0], ![192, 1, 0]] where
    su := ![![1666, 0, 0], ![0, 833, 0]]
    hsu := by decide
    w := ![![368186, 95795, 16660], ![94129, 24157, 4165]]
    hw := by decide
    g := ![![![-2054680, 396439496, 6162272], ![2558, -1711057527, 0]], ![![-831617, 160440639, 2493896], ![1375, -692471781, 0]]]
    h := ![![![0, 222, 673], ![113, -442, 0]], ![![0, 56, 172], ![30, -113, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {833} * I2N0 =  Ideal.span {B.equivFun.symm ![442, 115, 20]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 17 ![![3, 0, 0], ![-52, -3, 1]]
  ![170, 18, -5] ![![17, 0, 0], ![5, 1, 0]] where
    su := ![![51, 0, 0], ![-884, -51, 17]]
    hsu := by decide
    w := ![![2890, 306, -85], ![-1513, -102, 34]]
    hw := by decide
    g := ![![![-10, 103, 51], ![8, -287, 0]], ![![292, -1875, -936], ![-11, 5299, 0]]]
    h := ![![![1858, -992, 1631], ![-30098, 0, 900]], ![![-607, 332, -544], ![10034, 0, -300]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {17} * I3N0 =  Ideal.span {B.equivFun.symm ![170, 18, -5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS0 


noncomputable def E7RS0 : RelationCertificate Table 49 ![![7, 0, 0], ![-50, -3, 1]]
  ![1070, 11, -13] ![![49, 0, 0], ![-4, 1, 0]] where
    su := ![![343, 0, 0], ![-2450, -147, 49]]
    hsu := by decide
    w := ![![52430, 539, -637], ![-10388, 49, 98]]
    hw := by decide
    g := ![![![-46528, -139840, 139819], ![993, -2283712, 0]], ![![335631, 1008687, -1008548], ![-6783, 16472952, 0]]]
    h := ![![![10, -7, 1], ![-20, 0, 0]], ![![34, 4, -1], ![9, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {49} * I7N0 =  Ideal.span {B.equivFun.symm ![1070, 11, -13]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![3, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![3, 1, 0]] where
    su := ![![7, 0, 0], ![3, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![3, 1, 0]]
    hw := by decide
    g := ![![![16, -60, -45], ![0, 105, 0]], ![![6, -24, -18], ![1, 42, 0]]]
    h := ![![![16, -60, -45], ![0, 105, 0]], ![![6, -24, -18], ![1, 42, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E17RS0 : RelationCertificate Table 1 ![![17, 0, 0], ![5, 1, 0]]
  ![1, 0, 0] ![![17, 0, 0], ![5, 1, 0]] where
    su := ![![17, 0, 0], ![5, 1, 0]]
    hsu := by decide
    w := ![![17, 0, 0], ![5, 1, 0]]
    hw := by decide
    g := ![![![-32, 167, 84], ![17, -476, 0]], ![![-8, 48, 24], ![1, -136, 0]]]
    h := ![![![-32, 167, 84], ![17, -476, 0]], ![![-8, 48, 24], ![1, -136, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {1} * I17N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 17 ![![17, 0, 0], ![7, 1, 0]]
  ![391, 22, -8] ![![17, 0, 0], ![5, 1, 0]] where
    su := ![![289, 0, 0], ![119, 17, 0]]
    hsu := by decide
    w := ![![6647, 374, -136], ![-1819, -85, 34]]
    hw := by decide
    g := ![![![-14, 43, 22], ![-1, -126, 0]], ![![-17, 28, 15], ![9, -87, 0]]]
    h := ![![![-445, 3638, 1364], ![32, -7732, 0]], ![![118, -998, -374], ![1, 2120, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {17} * I17N1 =  Ideal.span {B.equivFun.symm ![391, 22, -8]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 119 ![![19, 0, 0], ![0, 1, 0]]
  ![169, 38, 6] ![![119, 0, 0], ![-43, -2, 1]] where
    su := ![![2261, 0, 0], ![0, 119, 0]]
    hsu := by decide
    w := ![![20111, 4522, 714], ![2975, 714, 119]]
    hw := by decide
    g := ![![![2990659, 204402, -41158], ![-1084408, -854604, 0]], ![![55417, 3787, -763], ![-19997, -15826, 0]]]
    h := ![![![0, 10, 27], ![17, -169, 0]], ![![0, 1, 4], ![12, -25, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {119} * I19N0 =  Ideal.span {B.equivFun.symm ![169, 38, 6]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E19RS0 


noncomputable def E23RS0 : RelationCertificate Table 17 ![![23, 0, 0], ![5, 1, 0]]
  ![-107, -5, 2] ![![17, 0, 0], ![-43, -2, 1]] where
    su := ![![391, 0, 0], ![85, 17, 0]]
    hsu := by decide
    w := ![![-1819, -85, 34], ![-306, 17, 0]]
    hw := by decide
    g := ![![![26, 0, -1], ![12, 0, 0]], ![![26, 0, -1], ![13, 0, 0]]]
    h := ![![![25079, -149126, -74585], ![-1021, 571819, 0]], ![![4247, -25271, -12639], ![-160, 96899, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {17} * I23N0 =  Ideal.span {B.equivFun.symm ![-107, -5, 2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 833 ![![23, 0, 0], ![-4, 1, 0]]
  ![-4533, -229, 88] ![![833, 0, 0], ![314, -2, 1]] where
    su := ![![19159, 0, 0], ![-3332, 833, 0]]
    hsu := by decide
    w := ![![-3775989, -190757, 73304], ![-1643509, -81634, 31654]]
    hw := by decide
    g := ![![![1495, 1442, -27], ![663, -3095, 0]], ![![-403, -200, 3], ![416, 430, 0]]]
    h := ![![![16389, 50127, -50104], ![-670, 384160, 0]], ![![7134, 21819, -21809], ![-290, 167215, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {833} * I23N1 =  Ideal.span {B.equivFun.symm ![-4533, -229, 88]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 119 ![![23, 0, 0], ![-1, 1, 0]]
  ![-1047, -40, 18] ![![119, 0, 0], ![-43, -2, 1]] where
    su := ![![2737, 0, 0], ![-119, 119, 0]]
    hsu := by decide
    w := ![![-124593, -4760, 2142], ![3213, 476, -119]]
    hw := by decide
    g := ![![![-687, -45, 10], ![325, 207, 0]], ![![88, 7, -1], ![83, -12, 0]]]
    h := ![![![2730090, 5149, -8205858], ![-118467, 62911584, 0]], ![![-70051, -132, 210553], ![3040, -1614240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {119} * I23N2 =  Ideal.span {B.equivFun.symm ![-1047, -40, 18]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E23RS2 


noncomputable def E31RS1 : RelationCertificate Table 7 ![![31, 0, 0], ![4, 1, 0]]
  ![-50, -3, 1] ![![7, 0, 0], ![3, 1, 0]] where
    su := ![![217, 0, 0], ![28, 7, 0]]
    hsu := by decide
    w := ![![-350, -21, 7], ![322, 14, -7]]
    hw := by decide
    g := ![![![31, -101, -76], ![0, 177, 0]], ![![3, -16, -12], ![-1, 28, 0]]]
    h := ![![![150, -769, -461], ![16, 4764, 0]], ![![-142, 708, 425], ![14, -4392, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {7} * I31N1 =  Ideal.span {B.equivFun.symm ![-50, -3, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E31RS1 
