import IdealArithmetic.Examples.NF3_3_936117_1.PrimesBelow3_3_936117_1F4
import IdealArithmetic.Examples.NF3_3_936117_1.ClassGroupData3_3_936117_1

set_option linter.all false

noncomputable section


noncomputable def E211RS0 : RelationCertificate Table 4 ![![211, 0, 0], ![30, 1, 0]]
  ![167, 7, -3] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![844, 0, 0], ![120, 4, 0]]
    hsu := by decide
    w := ![![668, 28, -12], ![-100, -24, 4]]
    hw := by decide
    g := ![![![-34, 167, 196], ![35, -795, 0]], ![![-6, 23, 28], ![5, -114, 0]]]
    h := ![![![14507, 484, 0], ![-102027, -3, 0]], ![![-2185, -103, -1], ![15367, 212, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N0 : Ideal.span {4} * I211N0 =  Ideal.span {B.equivFun.symm ![167, 7, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E211RS0 


noncomputable def E211RS1 : RelationCertificate Table 4 ![![211, 0, 0], ![77, 1, 0]]
  ![-325, -181, 25] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![844, 0, 0], ![308, 4, 0]]
    hsu := by decide
    w := ![![-1300, -724, 100], ![1900, 1144, -156]]
    hw := by decide
    g := ![![![29922, -512567, -542554], ![-120657, 2170125, 0]], ![![11021, -188931, -199978], ![-44476, 799875, 0]]]
    h := ![![![-6933, -177, -1], ![18994, 236, 0]], ![![9813, 143, 0], ![-26884, -39, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {4} * I211N1 =  Ideal.span {B.equivFun.symm ![-325, -181, 25]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E211RS1 


noncomputable def E211RS2 : RelationCertificate Table 4 ![![211, 0, 0], ![104, 1, 0]]
  ![581, 13, -9] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![844, 0, 0], ![416, 4, 0]]
    hsu := by decide
    w := ![![2324, 52, -36], ![-220, 0, 4]]
    hw := by decide
    g := ![![![-20892, 354591, 375472], ![83425, -1501875, 0]], ![![-10422, 176897, 187314], ![41623, -749250, 0]]]
    h := ![![![104783, 1324, 3], ![-212583, -642, 0]], ![![-10037, -201, -1], ![20363, 212, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N2 : Ideal.span {4} * I211N2 =  Ideal.span {B.equivFun.symm ![581, 13, -9]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E211RS2 
