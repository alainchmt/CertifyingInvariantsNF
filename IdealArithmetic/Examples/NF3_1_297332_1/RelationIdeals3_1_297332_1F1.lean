import IdealArithmetic.Examples.NF3_1_297332_1.PrimesBelow3_1_297332_1F1
import IdealArithmetic.Examples.NF3_1_297332_1.ClassGroupData3_1_297332_1

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 5 ![![37, 0, 0], ![9, 1, 0]]
  ![71, 3, -2] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![185, 0, 0], ![45, 5, 0]]
    hsu := by decide
    w := ![![355, 15, -10], ![-450, -5, 10]]
    hw := by decide
    g := ![![![7, -57, 64], ![-12, -158, 0]], ![![5, -15, 18], ![-3, -44, 0]]]
    h := ![![![1844, 223, 4], ![-7573, -75, 0]], ![![-2358, -289, -6], ![9684, 112, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {5} * I37N0 =  Ideal.span {B.equivFun.symm ![71, 3, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 5 ![![37, 0, 0], ![14, 1, 0]]
  ![1081, 103, -42] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![185, 0, 0], ![70, 5, 0]]
    hsu := by decide
    w := ![![5405, 515, -210], ![-8630, -595, 290]]
    hw := by decide
    g := ![![![-5885, -47900, 48170], ![-7223, -120913, 0]], ![![-3058, -20017, 19810], ![-2780, -49842, 0]]]
    h := ![![![2805, 223, 2], ![-7336, -58, 0]], ![![-4538, -377, -6], ![11870, 140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {5} * I37N1 =  Ideal.span {B.equivFun.symm ![1081, 103, -42]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E37RS1 


noncomputable def E41RS0 : RelationCertificate Table 20 ![![41, 0, 0], ![-18, 1, 0]]
  ![-1949, -637, -127] ![![20, 0, 0], ![-18, -2, 1]] where
    su := ![![820, 0, 0], ![-360, 20, 0]]
    hsu := by decide
    w := ![![-38980, -12740, -2540], ![-23900, -7820, -1560]]
    hw := by decide
    g := ![![![-20121838, -2209333, 34576], ![18332349, 4755961, 0]], ![![9324730, 1023834, -16024], ![-8495416, -2203971, 0]]]
    h := ![![![-19765, 1205, -17], ![-44912, 285, 0]], ![![-12119, 753, -12], ![-27538, 207, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {20} * I41N0 =  Ideal.span {B.equivFun.symm ![-1949, -637, -127]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 20 ![![41, 0, 0], ![-5, 1, 0]]
  ![-41, -13, -3] ![![20, 0, 0], ![-18, -2, 1]] where
    su := ![![820, 0, 0], ![-100, 20, 0]]
    hsu := by decide
    w := ![![-820, -260, -60], ![-340, -160, -40]]
    hw := by decide
    g := ![![![-53695068, -5895611, 92268], ![48919757, 12691278, 0]], ![![5341774, 586516, -9180], ![-4866677, -1262569, 0]]]
    h := ![![![-4241, 860, -5], ![-34768, 101, 0]], ![![-1757, 361, -4], ![-14404, 81, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {20} * I41N1 =  Ideal.span {B.equivFun.symm ![-41, -13, -3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E41RS1 


noncomputable def E53RS1 : RelationCertificate Table 10 ![![53, 0, 0], ![23, 1, 0]]
  ![-3, 1, 1] ![![10, 0, 0], ![-18, -2, 1]] where
    su := ![![530, 0, 0], ![230, 10, 0]]
    hsu := by decide
    w := ![![-30, 10, 10], ![-100, 30, 10]]
    hw := by decide
    g := ![![![-38247, -4132, -2703], ![69419, 10598, 0]], ![![-19115, -2065, -1352], ![34715, 5299, 0]]]
    h := ![![![-398, -29, -1], ![917, 27, 0]], ![![-1296, -91, -3], ![2986, 80, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {10} * I53N1 =  Ideal.span {B.equivFun.symm ![-3, 1, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 100 ![![61, 0, 0], ![18, 1, 0]]
  ![-6781, -413, 217] ![![100, 0, 0], ![2, -2, 1]] where
    su := ![![6100, 0, 0], ![1800, 100, 0]]
    hsu := by decide
    w := ![![-678100, -41300, 21700], ![-144000, -200, 2900]]
    hw := by decide
    g := ![![![730742463572781, 175838547922165, -19095061046577], ![10907127702587, -474649744238367, 0]], ![![203649559765974, 49004190476566, -5321574931927], ![3039691636564, -132279450388845, 0]]]
    h := ![![![-28987, -1778, -15], ![97857, 566, 0]], ![![-6156, -390, -5], ![20782, 167, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {100} * I61N1 =  Ideal.span {B.equivFun.symm ![-6781, -413, 217]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E61RS1 


noncomputable def E79RS1 : RelationCertificate Table 100 ![![79, 0, 0], ![11, 1, 0]]
  ![-437, -1, 9] ![![100, 0, 0], ![2, -2, 1]] where
    su := ![![7900, 0, 0], ![1100, 100, 0]]
    hsu := by decide
    w := ![![-43700, -100, 900], ![-3800, 900, -100]]
    hw := by decide
    g := ![![![-11577, -2784, 302], ![-109, 7520, 0]], ![![-1615, -388, 42], ![-1, 1049, 0]]]
    h := ![![![-1929, -181, -1], ![13814, 44, 0]], ![![-184, -22, -1], ![1318, 39, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {100} * I79N1 =  Ideal.span {B.equivFun.symm ![-437, -1, 9]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E79RS1 
