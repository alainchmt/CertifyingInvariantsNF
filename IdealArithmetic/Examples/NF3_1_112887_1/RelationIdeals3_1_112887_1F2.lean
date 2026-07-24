import IdealArithmetic.Examples.NF3_1_112887_1.PrimesBelow3_1_112887_1F2
import IdealArithmetic.Examples.NF3_1_112887_1.ClassGroupData3_1_112887_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 195 ![![83, 0, 0], ![-37, 1, 0]]
  ![-113, -16, 1] ![![195, 0, 0], ![16, 1, 0]] where
    su := ![![16185, 0, 0], ![-7215, 195, 0]]
    hsu := by decide
    w := ![![-22035, -3120, 195], ![-1755, -390, 0]]
    hw := by decide
    g := ![![![-170900, 408876535, 25555451], ![2082836, -4983312947, 0]], ![![74882, -179190984, -11199729], ![-912621, 2183947156, 0]]]
    h := ![![![-732, 57, -1], ![-1639, 84, 0]], ![![-38, 38, -1], ![-85, 83, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {195} * I83N1 =  Ideal.span {B.equivFun.symm ![-113, -16, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 13 ![![89, 0, 0], ![-10, 1, 0]]
  ![-22, 10, 1] ![![13, 0, 0], ![3, 1, 0]] where
    su := ![![1157, 0, 0], ![-130, 13, 0]]
    hsu := by decide
    w := ![![-286, 130, 13], ![-13, -13, 13]]
    hw := by decide
    g := ![![![5, 747, 251], ![66, -3252, 0]], ![![-2, -75, -25], ![1, 324, 0]]]
    h := ![![![-18, 2, 0], ![-158, 1, 0]], ![![1, 0, 0], ![9, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {13} * I89N1 =  Ideal.span {B.equivFun.symm ![-22, 10, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E89RS1 
