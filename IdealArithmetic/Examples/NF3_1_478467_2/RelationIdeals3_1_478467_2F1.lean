import IdealArithmetic.Examples.NF3_1_478467_2.PrimesBelow3_1_478467_2F1
import IdealArithmetic.Examples.NF3_1_478467_2.ClassGroupData3_1_478467_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 5 ![![37, 0, 0], ![-10, 1, 0]]
  ![17, 2, 0] ![![5, 0, 0], ![-119, -6, 1]] where
    su := ![![185, 0, 0], ![-50, 5, 0]]
    hsu := by decide
    w := ![![85, 10, 0], ![-145, 20, 5]]
    hw := by decide
    g := ![![![9, -2, 0], ![4, 0, 0]], ![![115, 7, -1], ![3, 0, 0]]]
    h := ![![![921, -92, 0], ![3406, 0, 0]], ![![-1557, 166, -1], ![-5758, 38, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {5} * I37N1 =  Ideal.span {B.equivFun.symm ![17, 2, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 10 ![![43, 0, 0], ![-1, 1, 0]]
  ![90905, 7663, -872] ![![10, 0, 0], ![-119, -11, 1]] where
    su := ![![430, 0, 0], ![-10, 10, 0]]
    hsu := by decide
    w := ![![909050, 76630, -8720], ![5384750, 375240, -46580]]
    hw := by decide
    g := ![![![52595, -1106989, -169667], ![575061, 0, 0]], ![![17788, -373527, -57251], ![194046, 0, 0]]]
    h := ![![![4322, -2030, -20], ![94941, -12, 0]], ![![25602, -12213, -102], ![562411, -272, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {10} * I43N1 =  Ideal.span {B.equivFun.symm ![90905, 7663, -872]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 5 ![![47, 0, 0], ![-10, 1, 0]]
  ![13198, 3381, 218] ![![5, 0, 0], ![-119, -6, 1]] where
    su := ![![235, 0, 0], ![-50, 5, 0]]
    hsu := by decide
    w := ![![65990, 16905, 1090], ![375985, 96315, 6210]]
    hw := by decide
    g := ![![![31, 144, -2], ![-313, 0, 0]], ![![69, -50, 0], ![124, 0, 0]]]
    h := ![![![694694, -72053, 273], ![3263742, -12613, 0]], ![![3958081, -410554, 1558], ![18595461, -71984, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {5} * I47N1 =  Ideal.span {B.equivFun.symm ![13198, 3381, 218]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E47RS1 


noncomputable def E59RS1 : RelationCertificate Table 10 ![![59, 0, 0], ![24, 1, 0]]
  ![-119, -8, 1] ![![10, 0, 0], ![-119, -11, 1]] where
    su := ![![590, 0, 0], ![240, 10, 0]]
    hsu := by decide
    w := ![![-1190, -80, 10], ![-3680, -220, 30]]
    hw := by decide
    g := ![![![112, 9, -1], ![7, 0, 0]], ![![114, 10, -1], ![9, 0, 0]]]
    h := ![![![-17005, -877, -7], ![41799, 414, 0]], ![![-52480, -2692, -21], ![128998, 1242, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {10} * I59N1 =  Ideal.span {B.equivFun.symm ![-119, -8, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 10 ![![61, 0, 0], ![-9, 1, 0]]
  ![34813, 8918, 575] ![![10, 0, 0], ![-119, -11, 1]] where
    su := ![![610, 0, 0], ![-90, 10, 0]]
    hsu := by decide
    w := ![![348130, 89180, 5750], ![-1707920, -437520, -28210]]
    hw := by decide
    g := ![![![-42, 333, -5], ![799, 0, 0]], ![![63, -86, 1], ![-210, 0, 0]]]
    h := ![![![3374086, -381777, 797], ![22864937, -48042, 0]], ![![-16553174, 1872996, -3911], ![-112174758, 235750, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {10} * I61N1 =  Ideal.span {B.equivFun.symm ![34813, 8918, 575]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E61RS1 


noncomputable def E71RS0 : RelationCertificate Table 2 ![![71, 0, 0], ![3, 1, 0]]
  ![98989, 25358, 1635] ![![2, 0, 0], ![-119, -7, 1]] where
    su := ![![142, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![197978, 50716, 3270], ![1284616, 329080, 21218]]
    hw := by decide
    g := ![![![61, 18, -20], ![689, 0, 0]], ![![63, -2, 1], ![-42, 0, 0]]]
    h := ![![![98939, 32929, 42], ![-2308560, -1347, 0]], ![![641992, 213679, 276], ![-14979708, -8987, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {2} * I71N0 =  Ideal.span {B.equivFun.symm ![98989, 25358, 1635]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 10 ![![71, 0, 0], ![27, 1, 0]]
  ![-755, -246, 19] ![![10, 0, 0], ![-119, -11, 1]] where
    su := ![![710, 0, 0], ![270, 10, 0]]
    hsu := by decide
    w := ![![-7550, -2460, 190], ![-337400, -26480, 3110]]
    hw := by decide
    g := ![![![498, -9749, -1495], ![5069, 0, 0]], ![![287, -5838, -895], ![3034, 0, 0]]]
    h := ![![![-105886, -4850, -34], ![278413, 2433, 0]], ![![-4711204, -215883, -1528], ![12387472, 108799, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {10} * I71N1 =  Ideal.span {B.equivFun.symm ![-755, -246, 19]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 5 ![![71, 0, 0], ![-30, 1, 0]]
  ![66749, 5126, -608] ![![5, 0, 0], ![-119, -6, 1]] where
    su := ![![355, 0, 0], ![-150, 5, 0]]
    hsu := by decide
    w := ![![333745, 25630, -3040], ![295655, -2080, -1095]]
    hw := by decide
    g := ![![![32457, -794974, -96758], ![164042, 0, 0]], ![![-6561, 162251, 19747], ![-33477, 0, 0]]]
    h := ![![![11708629, -437031, 1553], ![27708197, -110871, 0]], ![![10379291, -387447, 1380], ![24562351, -98199, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {5} * I71N2 =  Ideal.span {B.equivFun.symm ![66749, 5126, -608]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E71RS2 
