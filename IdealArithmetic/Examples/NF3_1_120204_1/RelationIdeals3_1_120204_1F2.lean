import IdealArithmetic.Examples.NF3_1_120204_1.PrimesBelow3_1_120204_1F2
import IdealArithmetic.Examples.NF3_1_120204_1.ClassGroupData3_1_120204_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 847 ![![89, 0, 0], ![-38, 1, 0]]
  ![-209, -47, 10] ![![847, 0, 0], ![-240, 1, 0]] where
    su := ![![75383, 0, 0], ![-32186, 847, 0]]
    hsu := by decide
    w := ![![-177023, -39809, 8470], ![50820, 11011, -2541]]
    hw := by decide
    g := ![![![61505033, 198612070048, -2482654079], ![217061513, 700936001634, 0]], ![![-25799648, -83312860501, 1041412100], ![-91051258, -294025349565, 0]]]
    h := ![![![-7096025, 214035, -2155], ![-16619632, 63935, 0]], ![![2037284, -61403, 615], ![4771532, -18246, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {847} * I89N1 =  Ideal.span {B.equivFun.symm ![-209, -47, 10]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 7 ![![97, 0, 0], ![-12, 1, 0]]
  ![13, -9, 4] ![![7, 0, 0], ![-2, 1, 0]] where
    su := ![![679, 0, 0], ![-84, 7, 0]]
    hsu := by decide
    w := ![![91, -63, 28], ![238, 7, -35]]
    hw := by decide
    g := ![![![-25, -2653, 4079], ![-370, -9504, 0]], ![![-306, -7997, 12219], ![-1050, -28512, 0]]]
    h := ![![![1105, -84, -2], ![8931, 66, 0]], ![![2890, -233, -2], ![23358, 63, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {7} * I97N1 =  Ideal.span {B.equivFun.symm ![13, -9, 4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E97RS1 
