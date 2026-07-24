import IdealArithmetic.Examples.NF3_1_251451_1.PrimesBelow3_1_251451_1F3
import IdealArithmetic.Examples.NF3_1_251451_1.ClassGroupData3_1_251451_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 7 ![![139, 0, 0], ![-31, 1, 0]]
  ![522763, 18032, 13870] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![973, 0, 0], ![-217, 7, 0]]
    hsu := by decide
    w := ![![3659341, 126224, 97090], ![679630, 23443, 18032]]
    hw := by decide
    g := ![![![-103, 113, 28], ![21, -394, 0]], ![![13, -19, -4], ![-2, 78, 0]]]
    h := ![![![1469566, -48742, 151], ![6572481, -7119, 0]], ![![272990, -9053, 28], ![1220920, -1316, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {7} * I139N1 =  Ideal.span {B.equivFun.symm ![522763, 18032, 13870]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E139RS1 
