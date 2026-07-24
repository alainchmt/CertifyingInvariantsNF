import IdealArithmetic.Examples.NF3_1_280904_4.PrimesBelow3_1_280904_4F3
import IdealArithmetic.Examples.NF3_1_280904_4.ClassGroupData3_1_280904_4

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 7 ![![139, 0, 0], ![61, 1, 0]]
  ![1, -4, -2] ![![7, 0, 0], ![2, 1, 0]] where
    su := ![![973, 0, 0], ![427, 7, 0]]
    hsu := by decide
    w := ![![7, -28, -14], ![196, 7, -14]]
    hw := by decide
    g := ![![![115, 332, 338], ![84, -1188, 0]], ![![53, 149, 152], ![38, -534, 0]]]
    h := ![![![-484, -42879, -1406], ![-499, 97716, 0]], ![![-12832, -1153105, -37810], ![-13838, 2627794, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {7} * I139N1 =  Ideal.span {B.equivFun.symm ![1, -4, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS1 
