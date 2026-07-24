import IdealArithmetic.Examples.NF3_1_329427_1.PrimesBelow3_1_329427_1F3
import IdealArithmetic.Examples.NF3_1_329427_1.ClassGroupData3_1_329427_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 50 ![![139, 0, 0], ![40, 1, 0]]
  ![69, 17, 6] ![![50, 0, 0], ![12, 1, 0]] where
    su := ![![6950, 0, 0], ![2000, 50, 0]]
    hsu := by decide
    w := ![![3450, 850, 300], ![1500, 350, 100]]
    hw := by decide
    g := ![![![-438488737863, 96613750102630, 14869275542721], ![1827037705009, -371731887803584, -138990]], ![![-175395420466, 38645483585600, 5947707684523], ![730814770839, -148692691807298, -55596]]]
    h := ![![![97631, 2686, 12], ![-339266, -831, 0]], ![![42410, 1142, 4], ![-147374, -277, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {50} * I139N1 =  Ideal.span {B.equivFun.symm ![69, 17, 6]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 5 ![![149, 0, 0], ![-44, 1, 0]]
  ![9, 2, 1] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![745, 0, 0], ![-220, 5, 0]]
    hsu := by decide
    w := ![![45, 10, 5], ![130, 25, 5]]
    hw := by decide
    g := ![![![-15785, 228952, 157897], ![39479, -394744, 0]], ![![4018, -58319, -40219], ![-10051, 100548, 0]]]
    h := ![![![1921, -22, -1], ![6505, 75, 0]], ![![5530, -104, -1], ![18726, 75, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {5} * I149N1 =  Ideal.span {B.equivFun.symm ![9, 2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E149RS1 


noncomputable def E151RS0 : RelationCertificate Table 25 ![![151, 0, 0], ![57, 1, 0]]
  ![-53, -4, 3] ![![25, 0, 0], ![12, 1, 0]] where
    su := ![![3775, 0, 0], ![1425, 25, 0]]
    hsu := by decide
    w := ![![-1325, -100, 75], ![-300, -75, 25]]
    hw := by decide
    g := ![![![-19, 617, 95], ![34, -1190, 0]], ![![-5, 247, 38], ![8, -476, 0]]]
    h := ![![![16564, 261, -1], ![-43881, 77, 0]], ![![3660, 35, -1], ![-9696, 76, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N0 : Ideal.span {25} * I151N0 =  Ideal.span {B.equivFun.symm ![-53, -4, 3]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E151RS0 


noncomputable def E151RS1 : RelationCertificate Table 25 ![![151, 0, 0], ![-29, 1, 0]]
  ![71, -22, 4] ![![25, 0, 0], ![12, 1, 0]] where
    su := ![![3775, 0, 0], ![-725, 25, 0]]
    hsu := by decide
    w := ![![1775, -550, 100], ![1300, -175, 0]]
    hw := by decide
    g := ![![![-71, 5437, 838], ![186, -10461, 0]], ![![5, -961, -148], ![-16, 1848, 0]]]
    h := ![![![36, 9351, -668], ![185, 50436, 0]], ![![28, 6803, -486], ![144, 36693, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {25} * I151N1 =  Ideal.span {B.equivFun.symm ![71, -22, 4]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E151RS1 


noncomputable def E151RS2 : RelationCertificate Table 25 ![![151, 0, 0], ![-28, 1, 0]]
  ![81, 8, -6] ![![25, 0, 0], ![12, 1, 0]] where
    su := ![![3775, 0, 0], ![-700, 25, 0]]
    hsu := by decide
    w := ![![2025, 200, -150], ![300, 125, -50]]
    hw := by decide
    g := ![![![63, -3754, -578], ![-114, 7232, 0]], ![![-16, 610, 94], ![31, -1176, 0]]]
    h := ![![![547, 7, -2], ![2947, 148, 0]], ![![108, 23, -2], ![582, 150, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N2 : Ideal.span {25} * I151N2 =  Ideal.span {B.equivFun.symm ![81, 8, -6]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E151RS2 


noncomputable def E157RS1 : RelationCertificate Table 4 ![![157, 0, 0], ![6, 1, 0]]
  ![1025, 271, 66] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![628, 0, 0], ![24, 4, 0]]
    hsu := by decide
    w := ![![4100, 1084, 264], ![7392, 1956, 476]]
    hw := by decide
    g := ![![![10507029, 19845242347527, 42171138018462], ![4961310586885, -84342276224559, -375245]], ![![456822, 862836623318, 1833527738896], ![215709155830, -3667055485950, -16315]]]
    h := ![![![23453, 3915, 2], ![-613516, -124, 0]], ![![42288, 7057, 3], ![-1106228, -176, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {4} * I157N1 =  Ideal.span {B.equivFun.symm ![1025, 271, 66]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E157RS1 
