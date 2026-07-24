import IdealArithmetic.Examples.NF3_1_542700_3.PrimesBelow3_1_542700_3F4
import IdealArithmetic.Examples.NF3_1_542700_3.ClassGroupData3_1_542700_3

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 561 ![![197, 0, 0], ![-88, 1, 0]]
  ![-7, 112, 13] ![![561, 0, 0], ![259, 1, 0]] where
    su := ![![110517, 0, 0], ![-49368, 561, 0]]
    hsu := by decide
    w := ![![-3927, 62832, 7293], ![-1683, 28611, 3927]]
    hw := by decide
    g := ![![![-34128734223, 50310497827277, 971247675646], ![73923628968, -108973989207457, 0]], ![![15333500389, -22603711015772, -436366220434], ![-33212717065, 48960289932684, 0]]]
    h := ![![![-427563, 5582, -41], ![-957158, 1618, 0]], ![![-183719, 2423, -19], ![-411280, 750, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {561} * I197N1 =  Ideal.span {B.equivFun.symm ![-7, 112, 13]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E197RS1 
