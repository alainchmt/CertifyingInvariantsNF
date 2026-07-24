import IdealArithmetic.Examples.NF3_1_547575_2.PrimesBelow3_1_547575_2F4
import IdealArithmetic.Examples.NF3_1_547575_2.ClassGroupData3_1_547575_2

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 4 ![![199, 0, 0], ![-17, 1, 0]]
  ![16147, 116, 395] ![![4, 0, 0], ![28, 0, 1]] where
    su := ![![796, 0, 0], ![-68, 4, 0]]
    hsu := by decide
    w := ![![64588, 464, 1580], ![450160, 3232, 11012]]
    hw := by decide
    g := ![![![-7, -47, 2], ![5, 0, 0]], ![![-3, 0, -1], ![1, -1, 0]]]
    h := ![![![205007, -12094, 7], ![2398838, -499, 0]], ![![1428646, -84298, 51], ![16716942, -3698, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {4} * I199N1 =  Ideal.span {B.equivFun.symm ![16147, 116, 395]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E199RS1 
