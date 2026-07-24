import IdealArithmetic.Examples.NF3_1_125083_1.PrimesBelow3_1_125083_1F2
import IdealArithmetic.Examples.NF3_1_125083_1.ClassGroupData3_1_125083_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 8 ![![89, 0, 0], ![4, 1, 0]]
  ![-29, 11, -1] ![![8, 0, 0], ![2, 1, 0]] where
    su := ![![712, 0, 0], ![32, 8, 0]]
    hsu := by decide
    w := ![![-232, 88, -8], ![-128, 0, 8]]
    hw := by decide
    g := ![![![-27, 62, 32], ![4, -267, 0]], ![![-4, 1, 1], ![7, -9, 0]]]
    h := ![![![-845, -215, -1], ![18794, 88, 0]], ![![-464, -120, -1], ![10320, 90, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {8} * I89N1 =  Ideal.span {B.equivFun.symm ![-29, 11, -1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E89RS1 
