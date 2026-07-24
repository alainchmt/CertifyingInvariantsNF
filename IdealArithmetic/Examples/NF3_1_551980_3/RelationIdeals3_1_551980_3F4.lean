import IdealArithmetic.Examples.NF3_1_551980_3.PrimesBelow3_1_551980_3F4
import IdealArithmetic.Examples.NF3_1_551980_3.ClassGroupData3_1_551980_3

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 9 ![![197, 0, 0], ![-93, 1, 0]]
  ![692, -53, -26] ![![9, 0, 0], ![-2, 1, 0]] where
    su := ![![1773, 0, 0], ![-837, 9, 0]]
    hsu := by decide
    w := ![![6228, -477, -234], ![2646, 252, -27]]
    hw := by decide
    g := ![![![2303, -689, 117], ![-586, -166, 0]], ![![-1160, 343, -57], ![298, 66, 0]]]
    h := ![![![647698, -8000, 11], ![1371998, -2193, 0]], ![![275070, -3424, 5], ![582672, -988, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {9} * I197N1 =  Ideal.span {B.equivFun.symm ![692, -53, -26]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E197RS1 
