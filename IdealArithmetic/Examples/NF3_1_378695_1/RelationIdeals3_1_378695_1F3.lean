import IdealArithmetic.Examples.NF3_1_378695_1.PrimesBelow3_1_378695_1F3
import IdealArithmetic.Examples.NF3_1_378695_1.ClassGroupData3_1_378695_1

set_option linter.all false

noncomputable section


noncomputable def E173RS1 : RelationCertificate Table 41 ![![173, 0, 0], ![69, 1, 0]]
  ![-482, 88, 19] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![7093, 0, 0], ![2829, 41, 0]]
    hsu := by decide
    w := ![![-19762, 3608, 779], ![-4961, 656, 164]]
    hw := by decide
    g := ![![![227599, -128229425, -42768438], ![-3110886, 1753505910, 0]], ![![92022, -51844667, -17291783], ![-1257763, 708963086, 0]]]
    h := ![![![-451120, -9305, -40], ![1131062, 6939, 0]], ![![-113333, -2334, -10], ![284152, 1734, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {41} * I173N1 =  Ideal.span {B.equivFun.symm ![-482, 88, 19]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E173RS1 
