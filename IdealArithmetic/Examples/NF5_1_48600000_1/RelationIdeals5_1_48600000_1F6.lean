import IdealArithmetic.Examples.NF5_1_48600000_1.PrimesBelow5_1_48600000_1F6
import IdealArithmetic.Examples.NF5_1_48600000_1.ClassGroupData5_1_48600000_1

set_option linter.all false

noncomputable section


noncomputable def E277RS1 : RelationCertificate Table 2 ![![277, 0, 0, 0, 0], ![-59, 1, 0, 0, 0]]
  ![-12, -11, 3, 9, 25] ![![2, 0, 0, 0, 0], ![6, -2, 1, 0, 1]] where
    su := ![![554, 0, 0, 0, 0], ![-118, 2, 0, 0, 0]]
    hsu := by decide
    w := ![![-24, -22, 6, 18, 50], ![10, 36, -28, -20, -72]]
    hw := by decide
    g := ![![![-232126427930, -419672583391, 170536437192, 157012576145, 327643701373], ![-27616631105, 156821445792, -190545696, -389664, 0]], ![![48799305876, 88226622657, -35851410093, -33008325669, -68879641772], ![5805769041, -32968144857, 40057902, 81918, 0]]]
    h := ![![![-896892, 26930475, -970849, 1613, -131], ![-4210524, 128543639, -197147, 4539, 0]], ![![685042, -20563295, 741378, -1233, 100], ![3215979, -98152013, 150846, -3467, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R277N1 : Ideal.span {2} * I277N1 =  Ideal.span {B.equivFun.symm ![-12, -11, 3, 9, 25]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E277RS1 
