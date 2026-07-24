import IdealArithmetic.Examples.NF3_3_260820_1.PrimesBelow3_3_260820_1F1
import IdealArithmetic.Examples.NF3_3_260820_1.ClassGroupData3_3_260820_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 5 ![![41, 0, 0], ![0, 1, 0]]
  ![41, -13, 1] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![205, 0, 0], ![0, 5, 0]]
    hsu := by decide
    w := ![![205, -65, 5], ![0, 115, -15]]
    hw := by decide
    g := ![![![33, 28, 2], ![-5, 6, 0]], ![![8, 7, -1], ![4, 8, 0]]]
    h := ![![![1, 0, 0], ![-13, 1, 0]], ![![0, 0, 0], ![23, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {5} * I41N1 =  Ideal.span {B.equivFun.symm ![41, -13, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E43RS0 : RelationCertificate Table 25 ![![43, 0, 0], ![10, 1, 0]]
  ![-1587, -84, 38] ![![25, 0, 0], ![-7, 1, 0]] where
    su := ![![1075, 0, 0], ![250, 25, 0]]
    hsu := by decide
    w := ![![-39675, -2100, 950], ![14225, 825, -350]]
    hw := by decide
    g := ![![![38, 276, -33], ![17, 903, 0]], ![![19, 67, -7], ![19, 207, 0]]]
    h := ![![![-4199, -447, -2], ![17897, 124, 0]], ![![1493, 152, 0], ![-6363, -14, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {25} * I43N0 =  Ideal.span {B.equivFun.symm ![-1587, -84, 38]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 25 ![![43, 0, 0], ![-9, 1, 0]]
  ![1957, 74, -43] ![![25, 0, 0], ![-7, 1, 0]] where
    su := ![![1075, 0, 0], ![-225, 25, 0]]
    hsu := by decide
    w := ![![48925, 1850, -1075], ![-17225, -625, 375]]
    hw := by decide
    g := ![![![-79183, -7623450, 1090677], ![-282742, -27266960, 0]], ![![16308, 1569752, -224583], ![58241, 5614576, 0]]]
    h := ![![![509047, -58570, 223], ![2431896, -9632, 0]], ![![-179219, 20625, -79], ![-856192, 3412, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {25} * I43N1 =  Ideal.span {B.equivFun.symm ![1957, 74, -43]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 25 ![![43, 0, 0], ![-1, 1, 0]]
  ![27, 14, 2] ![![25, 0, 0], ![-7, 1, 0]] where
    su := ![![1075, 0, 0], ![-25, 25, 0]]
    hsu := by decide
    w := ![![675, 350, 50], ![-25, 25, 0]]
    hw := by decide
    g := ![![![-36812, -3545351, 507230], ![-131491, -12680752, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![2, -1, 0], ![59, 2, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {25} * I43N2 =  Ideal.span {B.equivFun.symm ![27, 14, 2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS2 


noncomputable def E59RS1 : RelationCertificate Table 5 ![![59, 0, 0], ![11, 1, 0]]
  ![-331, -237, -31] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![295, 0, 0], ![55, 5, 0]]
    hsu := by decide
    w := ![![-1655, -1185, -155], ![-1880, -1345, -175]]
    hw := by decide
    g := ![![![-345, 80, -54], ![157, 314, 0]], ![![-53, 17, -11], ![27, 62, 0]]]
    h := ![![![-12796, -1227, -6], ![68603, 323, 0]], ![![-14526, -1395, -7], ![77878, 378, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {5} * I59N1 =  Ideal.span {B.equivFun.symm ![-331, -237, -31]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E79RS1 : RelationCertificate Table 25 ![![79, 0, 0], ![-23, 1, 0]]
  ![419, 183, -31] ![![25, 0, 0], ![-7, 1, 0]] where
    su := ![![1975, 0, 0], ![-575, 25, 0]]
    hsu := by decide
    w := ![![10475, 4575, -775], ![-5475, -2350, 400]]
    hw := by decide
    g := ![![![-121265, -11676491, 1670546], ![-433092, -41763636, 0]], ![![34696, 3340083, -477863], ![123913, 11946572, 0]]]
    h := ![![![276104, -12793, 34], ![948339, -2717, 0]], ![![-144294, 6714, -19], ![-495609, 1517, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {25} * I79N1 =  Ideal.span {B.equivFun.symm ![419, 183, -31]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E79RS1 
