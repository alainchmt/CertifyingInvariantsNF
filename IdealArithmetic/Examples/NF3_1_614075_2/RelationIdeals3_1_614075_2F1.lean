import IdealArithmetic.Examples.NF3_1_614075_2.PrimesBelow3_1_614075_2F1
import IdealArithmetic.Examples.NF3_1_614075_2.ClassGroupData3_1_614075_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 16 ![![37, 0, 0], ![-17, 1, 0]]
  ![726567, -55243, 15963] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![592, 0, 0], ![-272, 16, 0]]
    hsu := by decide
    w := ![![11625072, -883888, 255408], ![-1787856, 135936, -39280]]
    hw := by decide
    g := ![![![106, 30, 12], ![5, -275, 0]], ![![-33, -6, -4], ![2, 113, 0]]]
    h := ![![![245096878, -16398158, 116923], ![533403407, -4310188, 0]], ![![-37694202, 2521941, -17983], ![-82033749, 662916, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {16} * I37N1 =  Ideal.span {B.equivFun.symm ![726567, -55243, 15963]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 8 ![![43, 0, 0], ![17, 1, 0]]
  ![191, 85, 3] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![344, 0, 0], ![136, 8, 0]]
    hsu := by decide
    w := ![![1528, 680, 24], ![-336, 80, 88]]
    hw := by decide
    g := ![![![5149, -386, 97], ![-44, 129, 0]], ![![1741, -131, 32], ![-11, 50, 0]]]
    h := ![![![10310, 811, 12], ![-26067, -513, 0]], ![![-2226, -186, -3], ![5628, 140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {8} * I43N1 =  Ideal.span {B.equivFun.symm ![191, 85, 3]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E43RS1 


noncomputable def E59RS1 : RelationCertificate Table 4 ![![59, 0, 0], ![27, 1, 0]]
  ![-1, -3, -1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![236, 0, 0], ![108, 4, 0]]
    hsu := by decide
    w := ![![-4, -12, -4], ![112, 36, -4]]
    hw := by decide
    g := ![![![137, -10, 31122], ![-1, -124476, 0]], ![![57, -4, 14382], ![-1, -57523, 0]]]
    h := ![![![-65, -29, -1], ![142, 58, 0]], ![![1496, 56, 0], ![-3268, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {4} * I59N1 =  Ideal.span {B.equivFun.symm ![-1, -3, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS1 


noncomputable def E61RS0 : RelationCertificate Table 32 ![![61, 0, 0], ![18, 1, 0]]
  ![307, -23, 7] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![1952, 0, 0], ![576, 32, 0]]
    hsu := by decide
    w := ![![9824, -736, 224], ![4128, -320, 96]]
    hw := by decide
    g := ![![![48, -4110, -257], ![-99, 8225, 0]], ![![3, -1232, -77], ![-7, 2464, 0]]]
    h := ![![![1309, 70, 0], ![-4419, 7, 0]], ![![543, 29, 0], ![-1833, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {32} * I61N0 =  Ideal.span {B.equivFun.symm ![307, -23, 7]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E61RS0 


noncomputable def E61RS2 : RelationCertificate Table 2 ![![61, 0, 0], ![22, 1, 0]]
  ![24897, -1893, 547] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![122, 0, 0], ![44, 2, 0]]
    hsu := by decide
    w := ![![49794, -3786, 1094], ![-61264, 4658, -1346]]
    hw := by decide
    g := ![![![-139, -20, 5602], ![-9, -11178, 0]], ![![-74, -16, 2070], ![-6, -4131, 0]]]
    h := ![![![165899, 8658, 62], ![-458861, -3235, 0]], ![![-204132, -10669, -77], ![564610, 4024, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {2} * I61N2 =  Ideal.span {B.equivFun.symm ![24897, -1893, 547]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS2 


noncomputable def E71RS0 : RelationCertificate Table 2 ![![71, 0, 0], ![34, 1, 0]]
  ![82793, -6295, 1819] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![142, 0, 0], ![68, 2, 0]]
    hsu := by decide
    w := ![![165586, -12590, 3638], ![-203728, 15490, -4476]]
    hw := by decide
    g := ![![![-89, 25, 5546], ![13, -11037, 0]], ![![-86, -1, 2844], ![1, -5660, 0]]]
    h := ![![![681701, 24938, 173], ![-1421117, -10464, 0]], ![![-838848, -30725, -214], ![1748716, 12956, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {2} * I71N0 =  Ideal.span {B.equivFun.symm ![82793, -6295, 1819]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 32 ![![71, 0, 0], ![-19, 1, 0]]
  ![1091, 185, -105] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![2272, 0, 0], ![-608, 32, 0]]
    hsu := by decide
    w := ![![34912, 5920, -3360], ![29216, 7936, -1600]]
    hw := by decide
    g := ![![![-19142, 2603, -494], ![-9479, -982, 0]], ![![5784, -760, 151], ![2869, 243, 0]]]
    h := ![![![6124, -328, -1], ![22827, -34, 0]], ![![5126, -260, -1], ![19107, 21, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {32} * I71N1 =  Ideal.span {B.equivFun.symm ![1091, 185, -105]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 8 ![![73, 0, 0], ![19, 1, 0]]
  ![-67773, 5153, -1489] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![584, 0, 0], ![152, 8, 0]]
    hsu := by decide
    w := ![![-542184, 41224, -11912], ![166768, -12680, 3664]]
    hw := by decide
    g := ![![![-95, -41, -117360], ![-3, 938871, 0]], ![![-23, -12, -32114], ![4, 256905, 0]]]
    h := ![![![-6587794, -379659, -1760], ![25307431, 126991, 0]], ![![2026292, 116770, 541], ![-7784130, -39035, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {8} * I73N1 =  Ideal.span {B.equivFun.symm ![-67773, 5153, -1489]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E73RS1 


noncomputable def E73RS2 : RelationCertificate Table 8 ![![73, 0, 0], ![-21, 1, 0]]
  ![-494983, 37635, -10875] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![584, 0, 0], ![-168, 8, 0]]
    hsu := by decide
    w := ![![-3959864, 301080, -87000], ![1218000, -92608, 26760]]
    hw := by decide
    g := ![![![269, 84, -81814592], ![18, 654516661, 0]], ![![-63, -17, 24656453], ![5, -197251594, 0]]]
    h := ![![![-1481776, 74345, -320], ![-5127365, 12485, 0]], ![![455826, -22861, 98], ![1577288, -3809, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {8} * I73N2 =  Ideal.span {B.equivFun.symm ![-494983, 37635, -10875]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E73RS2 
