import IdealArithmetic.Examples.NF3_3_149769_2.PrimesBelow3_3_149769_2F1
import IdealArithmetic.Examples.NF3_3_149769_2.ClassGroupData3_3_149769_2

set_option linter.all false

noncomputable section


noncomputable def E43RS0 : RelationCertificate Table 169 ![![43, 0, 0], ![0, 1, 0]]
  ![-559, -51, 8] ![![169, 0, 0], ![-57, 1, 0]] where
    su := ![![7267, 0, 0], ![0, 169, 0]]
    hsu := by decide
    w := ![![-94471, -8619, 1352], ![36335, 3380, -507]]
    hw := by decide
    g := ![![![55, 168, -3], ![151, 500, 0]], ![![17, 57, -1], ![52, 170, 0]]]
    h := ![![![-13, -2, 0], ![35, 8, 0]], ![![5, 0, 0], ![20, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {169} * I43N0 =  Ideal.span {B.equivFun.symm ![-559, -51, 8]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS0 
