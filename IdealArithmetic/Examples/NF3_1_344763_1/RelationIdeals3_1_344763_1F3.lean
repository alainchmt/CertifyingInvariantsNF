import IdealArithmetic.Examples.NF3_1_344763_1.PrimesBelow3_1_344763_1F3
import IdealArithmetic.Examples.NF3_1_344763_1.ClassGroupData3_1_344763_1

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 5 ![![149, 0, 0], ![-69, 1, 0]]
  ![11635761, 2406774, 497824] ![![5, 0, 0], ![-1, 2, 1]] where
    su := ![![745, 0, 0], ![-345, 5, 0]]
    hsu := by decide
    w := ![![58178805, 12033870, 2489120], ![372837925, 77118860, 15951485]]
    hw := by decide
    g := ![![![-20319, -134, -192], ![3972, 0, 0]], ![![9843, -33, 122], ![-1956, 0, 0]]]
    h := ![![![432191751, -6993765, 14173], ![933115002, -1613953, 0]], ![![2769693469, -44819739, 90832], ![5979851584, -10343671, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {5} * I149N1 =  Ideal.span {B.equivFun.symm ![11635761, 2406774, 497824]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E149RS1 
