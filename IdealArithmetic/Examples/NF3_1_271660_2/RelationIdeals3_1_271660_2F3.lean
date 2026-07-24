import IdealArithmetic.Examples.NF3_1_271660_2.PrimesBelow3_1_271660_2F3
import IdealArithmetic.Examples.NF3_1_271660_2.ClassGroupData3_1_271660_2

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 5 ![![139, 0, 0], ![-24, 1, 0]]
  ![-1607, -626, -65] ![![5, 0, 0], ![-44, -7, 1]] where
    su := ![![695, 0, 0], ![-120, 5, 0]]
    hsu := by decide
    w := ![![-8035, -3130, -325], ![30010, 11695, 1215]]
    hw := by decide
    g := ![![![39, -132, 7], ![-156, 0, 0]], ![![14, 31, -2], ![34, 0, 0]]]
    h := ![![![-10157, 431, -1], ![-58759, 74, 0]], ![![38054, -1597, 3], ![220146, -174, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {5} * I139N1 =  Ideal.span {B.equivFun.symm ![-1607, -626, -65]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E139RS1 
