import IdealArithmetic.Examples.NF3_3_405405_1.PrimesBelow3_3_405405_1F2
import IdealArithmetic.Examples.NF3_3_405405_1.ClassGroupData3_3_405405_1

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 2 ![![97, 0, 0], ![-43, 1, 0]]
  ![-485, 1, 9] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![194, 0, 0], ![-86, 2, 0]]
    hsu := by decide
    w := ![![-970, 2, 18], ![-152, -52, 10]]
    hw := by decide
    g := ![![![-385, -503, 26], ![-444, -291, 0]], ![![143, 174, -22], ![161, 132, 0]]]
    h := ![![![-42446, 1163, -4], ![-95739, 397, 0]], ![![-6582, 198, -1], ![-14846, 102, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {2} * I97N1 =  Ideal.span {B.equivFun.symm ![-485, 1, 9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E97RS1 


noncomputable def E113RS1 : RelationCertificate Table 4 ![![113, 0, 0], ![-49, 1, 0]]
  ![81, 97, 13] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![452, 0, 0], ![-196, 4, 0]]
    hsu := by decide
    w := ![![324, 388, 52], ![400, 608, 84]]
    hw := by decide
    g := ![![![-78, -73, -13], ![4, 113, 0]], ![![40, 36, 5], ![3, -50, 0]]]
    h := ![![![1691, -28, 0], ![3898, 13, 0]], ![![2032, -31, 0], ![4684, 21, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {4} * I113N1 =  Ideal.span {B.equivFun.symm ![81, 97, 13]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E113RS1 
