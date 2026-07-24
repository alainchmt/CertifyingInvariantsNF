import IdealArithmetic.Examples.NF3_1_236763_2.PrimesBelow3_1_236763_2F2
import IdealArithmetic.Examples.NF3_1_236763_2.ClassGroupData3_1_236763_2

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 4 ![![89, 0, 0], ![-39, 1, 0]]
  ![-29, 13, 12] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![356, 0, 0], ![-156, 4, 0]]
    hsu := by decide
    w := ![![-116, 52, 48], ![532, -192, 92]]
    hw := by decide
    g := ![![![-3328809, 1886755, 83820], ![-1192714, 0, 334405]], ![![1444925, -818939, -36376], ![517732, 0, -145146]]]
    h := ![![![-790, 18948, -4212], ![601, 46860, 0]], ![![3699, -86798, 19295], ![-2570, -214654, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {4} * I89N1 =  Ideal.span {B.equivFun.symm ![-29, 13, 12]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 4 ![![97, 0, 0], ![-40, 1, 0]]
  ![-1797, -67, -96] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![388, 0, 0], ![-160, 4, 0]]
    hsu := by decide
    w := ![![-7188, -268, -384], ![-8240, -308, -440]]
    hw := by decide
    g := ![![![2773, -1570, -64], ![995, 0, -278]], ![![-1136, 642, 26], ![-405, 0, 114]]]
    h := ![![![-74637, 1753438, -379232], ![48959, 4598176, 0]], ![![-85596, 2010061, -434734], ![56038, 5271136, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {4} * I97N1 =  Ideal.span {B.equivFun.symm ![-1797, -67, -96]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS1 


noncomputable def E101RS0 : RelationCertificate Table 2 ![![101, 0, 0], ![4, 1, 0]]
  ![-5203, 1725, -1932] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![202, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![-10406, 3450, -3864], ![-87354, 36680, 19596]]
    hw := by decide
    g := ![![![490795571, 14238525, 26092257], ![7119263, 0, -49972]], ![![31986425, 934925, 1702812], ![467463, 0, -2418]]]
    h := ![![![-305865, -1073251, -1226868], ![-22693, 15488967, 0]], ![![-2570565, -9019879, -10310706], ![-191097, 130173888, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {2} * I101N0 =  Ideal.span {B.equivFun.symm ![-5203, 1725, -1932]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS0 


noncomputable def E101RS2 : RelationCertificate Table 4 ![![101, 0, 0], ![-9, 1, 0]]
  ![-9, 1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![404, 0, 0], ![-36, 4, 0]]
    hsu := by decide
    w := ![![-36, 4, 0], ![-16, -4, 8]]
    hw := by decide
    g := ![![![-997737, 565019, 25032], ![-357609, 0, 100130]], ![![64370, -36453, -1615], ![23072, 0, -6460]]]
    h := ![![![-3935, 11935, -15920], ![506, 200990, 0]], ![![-1735, 5270, -7030], ![253, 88754, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N2 : Ideal.span {4} * I101N2 =  Ideal.span {B.equivFun.symm ![-9, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E101RS2 


noncomputable def E107RS1 : RelationCertificate Table 4 ![![107, 0, 0], ![7, 1, 0]]
  ![7, 1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![428, 0, 0], ![28, 4, 0]]
    hsu := by decide
    w := ![![28, 4, 0], ![16, 12, 8]]
    hw := by decide
    g := ![![![5148775, -2915790, -129180], ![1845441, 0, -516722]], ![![340978, -193099, -8555], ![122216, 0, -34220]]]
    h := ![![![-2374, -11938, -9552], ![-213, 127758, 0]], ![![-1343, -6732, -5386], ![-53, 72038, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {4} * I107N1 =  Ideal.span {B.equivFun.symm ![7, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E107RS1 


noncomputable def E109RS0 : RelationCertificate Table 2 ![![109, 0, 0], ![46, 1, 0]]
  ![39, -13, 14] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![218, 0, 0], ![92, 2, 0]]
    hsu := by decide
    w := ![![78, -26, 28], ![632, -266, -146]]
    hw := by decide
    g := ![![![-1210624, 400811, 80358], ![200406, 0, 52635]], ![![-530070, 175568, 35209], ![87784, 0, 23055]]]
    h := ![![![-6301, -200725, -32778], ![-4486, 446602, 0]], ![![-51086, -1628600, -265949], ![-36487, 3623546, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N0 : Ideal.span {2} * I109N0 =  Ideal.span {B.equivFun.symm ![39, -13, 14]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS0 


noncomputable def E109RS1 : RelationCertificate Table 4 ![![109, 0, 0], ![-27, 1, 0]]
  ![-778313, -29047, -41596] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![436, 0, 0], ![-108, 4, 0]]
    hsu := by decide
    w := ![![-3113252, -116188, -166384], ![-3569732, -133224, -190780]]
    hw := by decide
    g := ![![![17713, -10036, -508], ![6352, 0, -1743]], ![![34619, -19608, -864], ![12412, 0, -3486]]]
    h := ![![![21724994, -284466086, 94845996], ![-7991153, -1292281895, 0]], ![![24910407, -326175874, 108752773], ![-9162896, -1481762494, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {4} * I109N1 =  Ideal.span {B.equivFun.symm ![-778313, -29047, -41596]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E109RS1 


noncomputable def E127RS1 : RelationCertificate Table 2 ![![127, 0, 0], ![31, 1, 0]]
  ![-75, -3, -4] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![254, 0, 0], ![62, 2, 0]]
    hsu := by decide
    w := ![![-150, -6, -8], ![-194, -8, -12]]
    hw := by decide
    g := ![![![333595, -107887, -21295], ![-53943, 0, -14196]], ![![95313, -30825, -6084], ![-15412, 0, -4056]]]
    h := ![![![1956, 37002, 8708], ![903, -138240, 0]], ![![2546, 47855, 11262], ![1101, -178785, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R127N1 : Ideal.span {2} * I127N1 =  Ideal.span {B.equivFun.symm ![-75, -3, -4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E127RS1 


noncomputable def E131RS1 : RelationCertificate Table 2 ![![131, 0, 0], ![1, 1, 0]]
  ![1, 1, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![262, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![2, 2, 0], ![2, 4, 8]]
    hw := by decide
    g := ![![![-3170913, 1025498, 202403], ![512751, 0, 134934]], ![![-24580, 7949, 1569], ![3976, 0, 1046]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![-3, -6, -12], ![0, 197, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {2} * I131N1 =  Ideal.span {B.equivFun.symm ![1, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E131RS1 
