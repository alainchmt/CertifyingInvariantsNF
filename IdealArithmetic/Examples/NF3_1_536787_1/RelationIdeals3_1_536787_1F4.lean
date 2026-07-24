import IdealArithmetic.Examples.NF3_1_536787_1.PrimesBelow3_1_536787_1F4
import IdealArithmetic.Examples.NF3_1_536787_1.ClassGroupData3_1_536787_1

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 20 ![![197, 0, 0], ![-67, 1, 0]]
  ![-199, 33, 1] ![![20, 0, 0], ![6, 1, 1]] where
    su := ![![3940, 0, 0], ![-1340, 20, 0]]
    hsu := by decide
    w := ![![-3980, 660, 20], ![3600, 140, -160]]
    hw := by decide
    g := ![![![-794, -90, -7], ![-243, 61, 0]], ![![247, 28, 2], ![80, -19, 0]]]
    h := ![![![-4925, 141, -1], ![-14478, 198, 0]], ![![4578, -71, 0], ![13458, -8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {20} * I197N1 =  Ideal.span {B.equivFun.symm ![-199, 33, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E197RS1 
