import IdealArithmetic.Examples.NF3_3_936117_1.PrimesBelow3_3_936117_1F3
import IdealArithmetic.Examples.NF3_3_936117_1.ClassGroupData3_3_936117_1

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 4 ![![149, 0, 0], ![16, 1, 0]]
  ![2029, 1737, 199] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![596, 0, 0], ![64, 4, 0]]
    hsu := by decide
    w := ![![8116, 6948, 796], ![19740, 16900, 1936]]
    hw := by decide
    g := ![![![-2714947750, 46154131148, 48869080087], ![10859795852, -195476320415, 0]], ![![-273316954, 4646390125, 4919707196], ![1093268297, -19678828791, 0]]]
    h := ![![![5849, 371, 1], ![-54342, 50, 0]], ![![14283, 915, 3], ![-132702, 37, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {4} * I149N1 =  Ideal.span {B.equivFun.symm ![2029, 1737, 199]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E149RS1 


noncomputable def E157RS1 : RelationCertificate Table 4 ![![157, 0, 0], ![39, 1, 0]]
  ![-6699, -5735, -657] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![628, 0, 0], ![156, 4, 0]]
    hsu := by decide
    w := ![![-26796, -22940, -2628], ![-65172, -55796, -6392]]
    hw := by decide
    g := ![![![-342, -417, -598], ![-186, 2355, 0]], ![![-90, -106, -144], ![-47, 570, 0]]]
    h := ![![![-567597, -16142, -44], ![2284770, 6251, 0]], ![![-1380435, -39258, -107], ![5556718, 15201, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {4} * I157N1 =  Ideal.span {B.equivFun.symm ![-6699, -5735, -657]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E157RS1 


noncomputable def E167RS1 : RelationCertificate Table 4 ![![167, 0, 0], ![-53, 1, 0]]
  ![-27, -23, 3] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![668, 0, 0], ![-212, 4, 0]]
    hsu := by decide
    w := ![![-108, -92, 12], ![240, 148, -20]]
    hw := by decide
    g := ![![![20059, -340544, -360584], ![-80119, 1442340, 0]], ![![-6352, 107839, 114185], ![25373, -456741, 0]]]
    h := ![![![-6264, 172, -1], ![-19737, 170, 0]], ![![14026, -266, 0], ![44194, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {4} * I167N1 =  Ideal.span {B.equivFun.symm ![-27, -23, 3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E167RS1 
