import IdealArithmetic.Examples.NF3_3_418605_1.PrimesBelow3_3_418605_1F3
import IdealArithmetic.Examples.NF3_3_418605_1.ClassGroupData3_3_418605_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 2 ![![139, 0, 0], ![-61, 1, 0]]
  ![-99, -55, -16] ![![2, 0, 0], ![-24, 0, 1]] where
    su := ![![278, 0, 0], ![-122, 2, 0]]
    hsu := by decide
    w := ![![-198, -110, -32], ![-2160, -1236, -362]]
    hw := by decide
    g := ![![![22, 67, -16], ![-3, 0, 0]], ![![13, -34, 7], ![4, 0, 0]]]
    h := ![![![-1473, -94657, 4580], ![124, -212212, 0]], ![![-16698, -1032186, 49943], ![-96, -2314086, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {2} * I139N1 =  Ideal.span {B.equivFun.symm ![-99, -55, -16]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS1 
