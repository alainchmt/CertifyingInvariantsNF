import IdealArithmetic.Examples.NF3_1_283015_1.PrimesBelow3_1_283015_1F2
import IdealArithmetic.Examples.NF3_1_283015_1.ClassGroupData3_1_283015_1

set_option linter.all false

noncomputable section


noncomputable def E97RS0 : RelationCertificate Table 3 ![![97, 0, 0], ![32, 1, 0]]
  ![-22136, 12017, 15774] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![291, 0, 0], ![96, 3, 0]]
    hsu := by decide
    w := ![![-66408, 36051, 47322], ![-1561626, -104763, 108153]]
    hw := by decide
    g := ![![![-12932776796, 741300457, -984068721], ![247100153, 0, 0]], ![![-3262124269, 186983371, -248218500], ![62327793, 0, 0]]]
    h := ![![![-1037752, -39110, -1695], ![3144994, 20021, 0]], ![![-24564894, -926926, -43014], ![74446068, 467601, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N0 : Ideal.span {3} * I97N0 =  Ideal.span {B.equivFun.symm ![-22136, 12017, 15774]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS0 


noncomputable def E97RS1 : RelationCertificate Table 3 ![![97, 0, 0], ![-28, 1, 0]]
  ![-481880132, 30690149, -36666771] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![291, 0, 0], ![-84, 3, 0]]
    hsu := by decide
    w := ![![-1445640396, 92070447, -110000313], ![3630010329, -231189357, 276211341]]
    hw := by decide
    g := ![![![84175, 3354, -7854], ![1121, 0, 0]], ![![-16282, 284, 2613], ![96, 0, 0]]]
    h := ![![![-34820345988, 1330872135, -29427801], ![-120610417168, 313092214, 0]], ![![87434064531, -3341826613, 73893345], ![302853366288, -786176002, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {3} * I97N1 =  Ideal.span {B.equivFun.symm ![-481880132, 30690149, -36666771]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS1 


noncomputable def E109RS1 : RelationCertificate Table 3 ![![109, 0, 0], ![-34, 1, 0]]
  ![1996, 173, -97] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![327, 0, 0], ![-102, 3, 0]]
    hsu := by decide
    w := ![![5988, 519, -291], ![9603, 2751, 1557]]
    hw := by decide
    g := ![![![2348975, -134643, 178736], ![-44878, 0, 0]], ![![-895046, 51303, -68105], ![17103, 0, 0]]]
    h := ![![![208404, -6600, 128], ![668060, -1561, 0]], ![![333939, -10543, 204], ![1070475, -2413, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {3} * I109N1 =  Ideal.span {B.equivFun.symm ![1996, 173, -97]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 
