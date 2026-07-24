import IdealArithmetic.Examples.NF3_1_344763_1.PrimesBelow3_1_344763_1F1
import IdealArithmetic.Examples.NF3_1_344763_1.ClassGroupData3_1_344763_1

set_option linter.all false

noncomputable section


noncomputable def E41RS1 : RelationCertificate Table 2 ![![41, 0, 0], ![18, 1, 0]]
  ![-6077, -1257, -260] ![![2, 0, 0], ![1, 1, 1]] where
    su := ![![82, 0, 0], ![36, 2, 0]]
    hsu := by decide
    w := ![![-12154, -2514, -520], ![-177498, -36714, -7594]]
    hw := by decide
    g := ![![![316, -55, -64], ![99, 0, 0]], ![![103, -11, -24], ![35, 0, 0]]]
    h := ![![![-30721, -2119, -28], ![69638, 888, 0]], ![![-448209, -30761, -400], ![1015990, 12603, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {2} * I41N1 =  Ideal.span {B.equivFun.symm ![-6077, -1257, -260]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E41RS1 


noncomputable def E43RS0 : RelationCertificate Table 5 ![![43, 0, 0], ![21, 1, 0]]
  ![-164, -34, -7] ![![5, 0, 0], ![-1, 2, 1]] where
    su := ![![215, 0, 0], ![105, 5, 0]]
    hsu := by decide
    w := ![![-820, -170, -35], ![-5260, -1085, -225]]
    hw := by decide
    g := ![![![1, 5, -3], ![7, 0, 0]], ![![-4, 3, -1], ![2, 0, 0]]]
    h := ![![![-4322, -371, -8], ![8842, 337, 0]], ![![-27638, -2327, -49], ![56542, 2062, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {5} * I43N0 =  Ideal.span {B.equivFun.symm ![-164, -34, -7]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E43RS0 


noncomputable def E43RS1 : RelationCertificate Table 10 ![![43, 0, 0], ![-18, 1, 0]]
  ![-1984, -397, 167] ![![10, 0, 0], ![-1, -3, 1]] where
    su := ![![430, 0, 0], ![-180, 10, 0]]
    hsu := by decide
    w := ![![-19840, -3970, 1670], ![-99490, 25220, -960]]
    hw := by decide
    g := ![![![-1126560, -187648, -65138], ![162443, 0, 0]], ![![344922, 57454, 19943], ![-49731, 0, 0]]]
    h := ![![![-15064, 913, -1], ![-35876, 210, 0]], ![![-75967, 4676, -25], ![-180924, 979, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {10} * I43N1 =  Ideal.span {B.equivFun.symm ![-1984, -397, 167]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E43RS1 


noncomputable def E43RS2 : RelationCertificate Table 2 ![![43, 0, 0], ![-3, 1, 0]]
  ![-3, 1, 0] ![![2, 0, 0], ![1, 1, 1]] where
    su := ![![86, 0, 0], ![-6, 2, 0]]
    hsu := by decide
    w := ![![-6, 2, 0], ![110, -2, -2]]
    hw := by decide
    g := ![![![3, 0, -1], ![3, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-15, 8, -1], ![-214, 43, 0]], ![![295, -98, 0], ![4210, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {2} * I43N2 =  Ideal.span {B.equivFun.symm ![-3, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E43RS2 


noncomputable def E53RS1 : RelationCertificate Table 5 ![![53, 0, 0], ![10, 1, 0]]
  ![281, 58, 12] ![![5, 0, 0], ![-1, 2, 1]] where
    su := ![![265, 0, 0], ![50, 5, 0]]
    hsu := by decide
    w := ![![1405, 290, 60], ![8985, 1860, 385]]
    hw := by decide
    g := ![![![61, -2, 0], ![-8, 0, 0]], ![![9, -1, -1], ![3, 0, 0]]]
    h := ![![![757, 74, 0], ![-3984, 12, 0]], ![![4849, 504, 3], ![-25520, -82, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {5} * I53N1 =  Ideal.span {B.equivFun.symm ![281, 58, 12]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS1 


noncomputable def E61RS0 : RelationCertificate Table 10 ![![61, 0, 0], ![16, 1, 0]]
  ![-1426, -295, -61] ![![10, 0, 0], ![-1, -3, 1]] where
    su := ![![610, 0, 0], ![160, 10, 0]]
    hsu := by decide
    w := ![![-14260, -2950, -610], ![-11230, -2320, -480]]
    hw := by decide
    g := ![![![-4, 20, -4], ![1, 0, 0]], ![![-8, 6, -1], ![3, 0, 0]]]
    h := ![![![-146778, -10073, -57], ![559502, 3416, 0]], ![![-115599, -7935, -45], ![440651, 2697, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {10} * I61N0 =  Ideal.span {B.equivFun.symm ![-1426, -295, -61]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![20, 1, 0]]
  ![-4776310740, -987945739, -204349515] ![![2, 0, 0], ![1, 1, 1]] where
    su := ![![122, 0, 0], ![40, 2, 0]]
    hsu := by decide
    w := ![![-9552621480, -1975891478, -408699030], ![-139505674442, -28855751674, -5968605994]]
    hw := by decide
    g := ![![![-45171, -55206, 34066], ![-33153, 0, 0]], ![![13273, -23428, 5677], ![-2239, 0, 0]]]
    h := ![![![-81904893660, -5010131785, -48480306], ![249571110126, 2752949151, 0]], ![![-1196132124941, -73167539826, -708002274], ![3644715339209, 40203835717, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![-4776310740, -987945739, -204349515]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 5 ![![61, 0, 0], ![25, 1, 0]]
  ![-1262, -261, -54] ![![5, 0, 0], ![-1, 2, 1]] where
    su := ![![305, 0, 0], ![125, 5, 0]]
    hsu := by decide
    w := ![![-6310, -1305, -270], ![-40435, -8365, -1730]]
    hw := by decide
    g := ![![![-5, -24, 6], ![-3, 0, 0]], ![![8, -10, 2], ![-1, 0, 0]]]
    h := ![![![-8542, -423, -4], ![20792, 190, 0]], ![![-54767, -2646, -23], ![133308, 1057, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {5} * I61N2 =  Ideal.span {B.equivFun.symm ![-1262, -261, -54]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E61RS2 


noncomputable def E71RS1 : RelationCertificate Table 10 ![![71, 0, 0], ![-31, 1, 0]]
  ![-353, 15, 12] ![![10, 0, 0], ![-1, -3, 1]] where
    su := ![![710, 0, 0], ![-310, 10, 0]]
    hsu := by decide
    w := ![![-3530, 150, 120], ![-2020, 2400, -410]]
    hw := by decide
    g := ![![![-10278, -1710, -595], ![1489, 0, 0]], ![![3788, 631, 219], ![-546, 0, 0]]]
    h := ![![![-124673, 4585, -18], ![-285530, 1290, 0]], ![![-72032, 2650, -11], ![-164970, 740, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {10} * I71N1 =  Ideal.span {B.equivFun.symm ![-353, 15, 12]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E71RS1 
