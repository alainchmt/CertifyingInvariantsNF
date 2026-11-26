import IdealArithmetic.Examples.NF3_1_116424_1.PrimesBelow3_1_116424_1F2
import IdealArithmetic.Examples.NF3_1_116424_1.ClassGroupData3_1_116424_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 320 ![![89, 0, 0], ![-23, 1, 0]]
  ![-35, -16, 17] ![![320, 0, 0], ![558, 179, 84]] where
    su := ![![28480, 0, 0], ![-7360, 320, 0]]
    hsu := by decide
    w := ![![-11200, -5120, 5440], ![23680, -20160, -26880]]
    hw := by decide
    g := ![![![-5131859, 4484947, -1169032], ![-6745504, 1293965, 0]], ![![1321367, -1155494, 301051], ![1737953, -333321, 0]]]
    h := ![![![-1244443, -13528858, 3220703], ![169636, -57328510, 0]], ![![2690985, 29254305, -6964331], ![-366633, 123965075, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {320} * I89N1 =  Ideal.span {B.equivFun.symm ![-35, -16, 17]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E89RS1 
