import IdealArithmetic.Examples.NF3_1_143468_1.PrimesBelow3_1_143468_1F1
import IdealArithmetic.Examples.NF3_1_143468_1.ClassGroupData3_1_143468_1

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 5 ![![41, 0, 0], ![19, 1, 0]]
  ![20, -8, 1] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![205, 0, 0], ![95, 5, 0]]
    hsu := by decide
    w := ![![100, -40, 5], ![-115, 50, -5]]
    hw := by decide
    g := ![![![17, 2, 0], ![3, 0, 0]], ![![9, 1, 0], ![2, 0, 0]]]
    h := ![![![70, 3, 0], ![-150, 1, 0]], ![![-128, -25, -1], ![275, 40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {5} * I41N0 =  Ideal.span {B.equivFun.symm ![20, -8, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 5 ![![41, 0, 0], ![-19, 1, 0]]
  ![-30, 2, 1] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![205, 0, 0], ![-95, 5, 0]]
    hsu := by decide
    w := ![![-150, 10, 5], ![-115, -50, -5]]
    hw := by decide
    g := ![![![4, -4, 1], ![-2, 0, 0]], ![![6, 1, -1], ![3, 0, 0]]]
    h := ![![![-238, 32, -1], ![-512, 42, 0]], ![![-204, 29, -1], ![-439, 40, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {5} * I41N1 =  Ideal.span {B.equivFun.symm ![-30, 2, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E61RS1 : RelationCertificate Table 5 ![![61, 0, 0], ![20, 1, 0]]
  ![-260, 114, -15] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![305, 0, 0], ![100, 5, 0]]
    hsu := by decide
    w := ![![-1300, 570, -75], ![1495, -650, 85]]
    hw := by decide
    g := ![![![-12, -16, -1], ![44, 0, 0]], ![![7, -9, -1], ![20, 0, 0]]]
    h := ![![![-11180, -692, -7], ![34086, 412, 0]], ![![12799, 772, 7], ![-39022, -410, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {5} * I61N1 =  Ideal.span {B.equivFun.symm ![-260, 114, -15]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 5 ![![61, 0, 0], ![-27, 1, 0]]
  ![55, -124, -20] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![305, 0, 0], ![-135, 5, 0]]
    hsu := by decide
    w := ![![275, -620, -100], ![24495, -2020, -865]]
    hw := by decide
    g := ![![![-98, 5304, -2017], ![4329, 0, 0]], ![![66, -2925, 1111], ![-2383, 0, 0]]]
    h := ![![![8239, -343, 1], ![18612, -81, 0]], ![![712659, -30282, 141], ![1609900, -8774, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {5} * I61N2 =  Ideal.span {B.equivFun.symm ![55, -124, -20]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS2 


noncomputable def E67RS1 : RelationCertificate Table 5 ![![67, 0, 0], ![31, 1, 0]]
  ![5, -2, 0] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![335, 0, 0], ![155, 5, 0]]
    hsu := by decide
    w := ![![25, -10, 0], ![115, 0, -5]]
    hw := by decide
    g := ![![![18, -6, -1], ![9, 0, 0]], ![![20, -5, -1], ![7, 0, 0]]]
    h := ![![![-30, -1, 0], ![65, 0, 0]], ![![110, 4, 0], ![-237, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {5} * I67N1 =  Ideal.span {B.equivFun.symm ![5, -2, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 5 ![![71, 0, 0], ![-14, 1, 0]]
  ![-25, 3, 1] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![355, 0, 0], ![-70, 5, 0]]
    hsu := by decide
    w := ![![-125, 15, 5], ![-345, -20, 5]]
    hw := by decide
    g := ![![![22, -1, -2], ![6, 0, 0]], ![![7, -2, 0], ![1, 0, 0]]]
    h := ![![![-1747, 139, -1], ![-8858, 72, 0]], ![![-4871, 362, -1], ![-24698, 72, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {5} * I71N1 =  Ideal.span {B.equivFun.symm ![-25, 3, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 5 ![![73, 0, 0], ![17, 1, 0]]
  ![-1395, 153, 55] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![365, 0, 0], ![85, 5, 0]]
    hsu := by decide
    w := ![![-6975, 765, 275], ![-17135, -1300, 195]]
    hw := by decide
    g := ![![![-149, 8039, -3057], ![6561, 0, 0]], ![![-18, 1143, -435], ![934, 0, 0]]]
    h := ![![![-80468, -5066, -19], ![345457, 1442, 0]], ![![-197984, -12472, -48], ![849965, 3543, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {5} * I73N1 =  Ideal.span {B.equivFun.symm ![-1395, 153, 55]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 


noncomputable def E73RS2 : RelationCertificate Table 5 ![![73, 0, 0], ![-19, 1, 0]]
  ![1540, -12, -37] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![365, 0, 0], ![-95, 5, 0]]
    hsu := by decide
    w := ![![7700, -60, -185], ![-12765, 4190, 925]]
    hw := by decide
    g := ![![![-211, 11418, -4342], ![9319, 0, 0]], ![![88, -4009, 1523], ![-3267, 0, 0]]]
    h := ![![![158162, -8770, 23], ![607594, -1716, 0]], ![![-262679, 14605, -38], ![-1009106, 2959, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {5} * I73N2 =  Ideal.span {B.equivFun.symm ![1540, -12, -37]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS2 


noncomputable def E79RS1 : RelationCertificate Table 5 ![![79, 0, 0], ![19, 1, 0]]
  ![-140, 61, -8] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![395, 0, 0], ![95, 5, 0]]
    hsu := by decide
    w := ![![-700, 305, -40], ![805, -350, 45]]
    hw := by decide
    g := ![![![-5, -23, -3], ![14, 0, 0]], ![![2, -7, -1], ![4, 0, 0]]]
    h := ![![![-756, -56, -1], ![3136, 71, 0]], ![![820, 40, 0], ![-3401, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {5} * I79N1 =  Ideal.span {B.equivFun.symm ![-140, 61, -8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 
