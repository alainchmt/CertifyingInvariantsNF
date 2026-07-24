import IdealArithmetic.Examples.NF3_1_603288_2.PrimesBelow3_1_603288_2F4
import IdealArithmetic.Examples.NF3_1_603288_2.ClassGroupData3_1_603288_2

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 4 ![![197, 0, 0], ![79, 1, 0]]
  ![64, 5, 2] ![![4, 0, 0], ![13, 0, 1]] where
    su := ![![788, 0, 0], ![316, 4, 0]]
    hsu := by decide
    w := ![![256, 20, 8], ![1532, 100, 48]]
    hw := by decide
    g := ![![![75732, 9481495, -1077775], ![-23297, 0, -541800]], ![![30372, 3803623, -432364], ![-9343, 0, -217350]]]
    h := ![![![30, 0, 0], ![-74, 1, 0]], ![![656, 6, 0], ![-1631, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {4} * I197N1 =  Ideal.span {B.equivFun.symm ![64, 5, 2]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E197RS1 
