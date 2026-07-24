import IdealArithmetic.Examples.NF3_1_226175_1.PrimesBelow3_1_226175_1F1
import IdealArithmetic.Examples.NF3_1_226175_1.ClassGroupData3_1_226175_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 9 ![![37, 0, 0], ![-9, 1, 0]]
  ![17, -15, 1] ![![9, 0, 0], ![0, 3, 0]] where
    su := ![![333, 0, 0], ![-81, 9, 0]]
    hsu := by decide
    w := ![![153, -135, 9], ![135, -54, -45]]
    hw := by decide
    g := ![![![986, 30, 27], ![10, 0, 0]], ![![-207, -7, 3], ![0, -26, 0]]]
    h := ![![![1448, -161, 0], ![5951, 1, 0]], ![![1284, -144, 0], ![5277, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {9} * I37N1 =  Ideal.span {B.equivFun.symm ![17, -15, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 3 ![![41, 0, 0], ![2, 1, 0]]
  ![2, 1, 0] ![![3, 0, 0], ![24, 1, 1]] where
    su := ![![123, 0, 0], ![6, 3, 0]]
    hsu := by decide
    w := ![![6, 3, 0], ![93, -9, 3]]
    hw := by decide
    g := ![![![-19, -2, -1], ![4, 0, 0]], ![![-23, -1, -1], ![3, 0, 0]]]
    h := ![![![6, 3, 0], ![-122, 0, 0]], ![![145, 72, 0], ![-2957, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {3} * I41N1 =  Ideal.span {B.equivFun.symm ![2, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E41RS1 


noncomputable def E43RS1 : RelationCertificate Table 3 ![![43, 0, 0], ![12, 1, 0]]
  ![-16, 13, 0] ![![3, 0, 0], ![24, 1, 1]] where
    su := ![![129, 0, 0], ![36, 3, 0]]
    hsu := by decide
    w := ![![-48, 39, 0], ![201, -159, -3]]
    hw := by decide
    g := ![![![33, -15, -28], ![253, 0, 0]], ![![1, -5, -9], ![79, 0, 0]]]
    h := ![![![-64, -17, -1], ![228, 43, 0]], ![![241, 19, 0], ![-858, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {3} * I43N1 =  Ideal.span {B.equivFun.symm ![-16, 13, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E43RS1 


noncomputable def E53RS0 : RelationCertificate Table 9 ![![53, 0, 0], ![20, 1, 0]]
  ![803, 27, 22] ![![9, 0, 0], ![0, 3, 0]] where
    su := ![![477, 0, 0], ![180, 9, 0]]
    hsu := by decide
    w := ![![7227, 243, 198], ![2970, 99, 81]]
    hw := by decide
    g := ![![![-14, 9, 32], ![6, -95, 0]], ![![-5, 3, 13], ![2, -38, 0]]]
    h := ![![![2191, 121, 1], ![-5766, -31, 0]], ![![890, 41, 0], ![-2342, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N0 : Ideal.span {9} * I53N0 =  Ideal.span {B.equivFun.symm ![803, 27, 22]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS0 


noncomputable def E53RS1 : RelationCertificate Table 3 ![![53, 0, 0], ![-16, 1, 0]]
  ![329, 11, 9] ![![3, 0, 0], ![24, 2, 1]] where
    su := ![![159, 0, 0], ![-48, 3, 0]]
    hsu := by decide
    w := ![![987, 33, 27], ![9201, 312, 252]]
    hw := by decide
    g := ![![![-16, 8, -2], ![1, 0, 0]], ![![-15, -3, 0], ![2, 0, 0]]]
    h := ![![![1445, -87, 0], ![4766, 9, 0]], ![![13487, -876, 4], ![44484, -128, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {3} * I53N1 =  Ideal.span {B.equivFun.symm ![329, 11, 9]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E53RS1 


noncomputable def E53RS2 : RelationCertificate Table 3 ![![53, 0, 0], ![-4, 1, 0]]
  ![-4, 1, 0] ![![3, 0, 0], ![24, 1, 1]] where
    su := ![![159, 0, 0], ![-12, 3, 0]]
    hsu := by decide
    w := ![![-12, 3, 0], ![-51, -15, -3]]
    hw := by decide
    g := ![![![-9, -1, 0], ![-1, 0, 0]], ![![-23, -1, -1], ![3, 0, 0]]]
    h := ![![![-44, 15, -1], ![-582, 53, 0]], ![![-189, 51, -1], ![-2500, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N2 : Ideal.span {3} * I53N2 =  Ideal.span {B.equivFun.symm ![-4, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS2 


noncomputable def E59RS1 : RelationCertificate Table 9 ![![59, 0, 0], ![3, 1, 0]]
  ![21071, 711, 577] ![![9, 0, 0], ![0, 3, 0]] where
    su := ![![531, 0, 0], ![27, 9, 0]]
    hsu := by decide
    w := ![![189639, 6399, 5193], ![77895, 2628, 2133]]
    hw := by decide
    g := ![![![-56, 32, 69525], ![12, -208552, 0]], ![![3, -4, 4777], ![1, -14328, 0]]]
    h := ![![![21043, 6923, 15], ![-406822, -308, 0]], ![![8643, 2843, 6], ![-167094, -117, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {9} * I59N1 =  Ideal.span {B.equivFun.symm ![21071, 711, 577]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS1 


noncomputable def E71RS1 : RelationCertificate Table 9 ![![71, 0, 0], ![26, 1, 0]]
  ![184, 6, 5] ![![9, 0, 0], ![0, 3, 0]] where
    su := ![![639, 0, 0], ![234, 9, 0]]
    hsu := by decide
    w := ![![1656, 54, 45], ![675, 27, 18]]
    hw := by decide
    g := ![![![-1, 2, -1], ![1, 0, 0]], ![![-1, 1, 0], ![1, -1, 0]]]
    h := ![![![25736, 1170, 7], ![-70272, -492, 0]], ![![10471, 454, 2], ![-28591, -140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {9} * I71N1 =  Ideal.span {B.equivFun.symm ![184, 6, 5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 3 ![![73, 0, 0], ![36, 1, 0]]
  ![1, -2, 0] ![![3, 0, 0], ![24, 2, 1]] where
    su := ![![219, 0, 0], ![108, 3, 0]]
    hsu := by decide
    w := ![![3, -6, 0], ![-66, 24, -3]]
    hw := by decide
    g := ![![![-15, 2, 0], ![-4, 0, 0]], ![![-8, 1, 0], ![-2, 0, 0]]]
    h := ![![![-35, -1, 0], ![71, 0, 0]], ![![-598, -52, -1], ![1212, 72, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {3} * I73N1 =  Ideal.span {B.equivFun.symm ![1, -2, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E73RS1 


noncomputable def E79RS0 : RelationCertificate Table 3 ![![79, 0, 0], ![-37, 1, 0]]
  ![-2, -7, 7] ![![3, 0, 0], ![24, 2, 1]] where
    su := ![![237, 0, 0], ![-111, 3, 0]]
    hsu := by decide
    w := ![![-6, -21, 21], ![267, -102, -93]]
    hw := by decide
    g := ![![![411, -1039, -292], ![2654, 0, 0]], ![![-215, 468, 131], ![-1198, 0, 0]]]
    h := ![![![-178, 8, 0], ![-380, 7, 0]], ![![11288, -320, 0], ![24099, -31, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N0 : Ideal.span {3} * I79N0 =  Ideal.span {B.equivFun.symm ![-2, -7, 7]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E79RS0 


noncomputable def E79RS1 : RelationCertificate Table 3 ![![79, 0, 0], ![-29, 1, 0]]
  ![328, 11, 9] ![![3, 0, 0], ![24, 1, 1]] where
    su := ![![237, 0, 0], ![-87, 3, 0]]
    hsu := by decide
    w := ![![984, 33, 27], ![8772, 297, 240]]
    hw := by decide
    g := ![![![-1, 13, 2], ![-2, 0, 0]], ![![-9, -6, -1], ![2, 0, 0]]]
    h := ![![![5092, -172, 0], ![13860, 9, 0]], ![![45150, -1670, 5], ![122894, -315, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {3} * I79N1 =  Ideal.span {B.equivFun.symm ![328, 11, 9]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E79RS1 


noncomputable def E79RS2 : RelationCertificate Table 9 ![![79, 0, 0], ![-13, 1, 0]]
  ![-229, 192, -5] ![![9, 0, 0], ![0, 3, 0]] where
    su := ![![711, 0, 0], ![-117, 9, 0]]
    hsu := by decide
    w := ![![-2061, 1728, -45], ![-675, -162, 576]]
    hw := by decide
    g := ![![![148484, 4509, 4066], ![1504, 0, 0]], ![![-22118, -672, -606], ![-223, 1, 0]]]
    h := ![![![-27282, 2165, -5], ![-165773, 390, 0]], ![![-8902, 708, -1], ![-54091, 143, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N2 : Ideal.span {9} * I79N2 =  Ideal.span {B.equivFun.symm ![-229, 192, -5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS2 
