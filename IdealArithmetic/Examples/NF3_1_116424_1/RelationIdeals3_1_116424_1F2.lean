import IdealArithmetic.Examples.NF3_1_116424_1.PrimesBelow3_1_116424_1F2
import IdealArithmetic.Examples.NF3_1_116424_1.ClassGroupData3_1_116424_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 320 ![![89, 0, 0], ![-23, 1, 0]]
  ![-35, -16, 17] ![![320, 0, 0], ![-1082, -66, -133]] where
    su := ![![28480, 0, 0], ![-7360, 320, 0]]
    hsu := by decide
    w := ![![-11200, -5120, 5440], ![176000, -27520, 14400]]
    hw := by decide
    g := ![![![-106374474032417, 137394505504279, 109119750023729], ![285988177458961, -48720431163258, 0]], ![![27492919610261, -35510174118072, -28202447462024], ![-73914818791233, 12591995490411, 0]]]
    h := ![![![-1244443, -13528858, 3220703], ![169636, -57328510, 0]], ![![19764219, 214862973, -51150645], ![-2693393, 910481490, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {320} * I89N1 =  Ideal.span {B.equivFun.symm ![-35, -16, 17]} * (J0 ^ 6*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6J1_1 E89RS1 
