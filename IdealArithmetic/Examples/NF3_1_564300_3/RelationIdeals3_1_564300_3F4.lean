import IdealArithmetic.Examples.NF3_1_564300_3.PrimesBelow3_1_564300_3F4
import IdealArithmetic.Examples.NF3_1_564300_3.ClassGroupData3_1_564300_3

set_option linter.all false

noncomputable section


noncomputable def E211RS0 : RelationCertificate Table 6 ![![211, 0, 0], ![6, 1, 0]]
  ![6, 1, 0] ![![6, 0, 0], ![18, 0, 1]] where
    su := ![![1266, 0, 0], ![36, 6, 0]]
    hsu := by decide
    w := ![![36, 6, 0], ![138, -12, 6]]
    hw := by decide
    g := ![![![-2, -1, -1], ![11, 0, 0]], ![![-17, 0, -1], ![6, 0, 0]]]
    h := ![![![198, 33, 0], ![-6962, 0, 0]], ![![767, 123, -4], ![-26969, 169, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N0 : Ideal.span {6} * I211N0 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E211RS0 


noncomputable def E211RS2 : RelationCertificate Table 6 ![![211, 0, 0], ![-36, 1, 0]]
  ![-6, 0, 1] ![![6, 0, 0], ![0, 1, 0]] where
    su := ![![1266, 0, 0], ![-216, 6, 0]]
    hsu := by decide
    w := ![![-36, 0, 6], ![30, -36, 0]]
    hw := by decide
    g := ![![![-36, -1, -1], ![5, 0, 0]], ![![6, 0, -29], ![0, 35, 0]]]
    h := ![![![-1266, 64, -4], ![-7420, 169, 0]], ![![1115, -31, 0], ![6535, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N2 : Ideal.span {6} * I211N2 =  Ideal.span {B.equivFun.symm ![-6, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E211RS2 
