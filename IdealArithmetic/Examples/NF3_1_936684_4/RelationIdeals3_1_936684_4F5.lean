import IdealArithmetic.Examples.NF3_1_936684_4.PrimesBelow3_1_936684_4F5
import IdealArithmetic.Examples.NF3_1_936684_4.ClassGroupData3_1_936684_4

set_option linter.all false

noncomputable section


noncomputable def E269RS1 : RelationCertificate Table 10 ![![269, 0, 0], ![-74, 1, 0]]
  ![-180, -16, 3] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![2690, 0, 0], ![-740, 10, 0]]
    hsu := by decide
    w := ![![-1800, -160, 30], ![690, 40, -10]]
    hw := by decide
    g := ![![![-5, -14, -6], ![1, 56, 0]], ![![6, -355, -179], ![-26, 1791, 0]]]
    h := ![![![-2756, 112, -1], ![-10016, 272, 0]], ![![1165, -16, 0], ![4234, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R269N1 : Ideal.span {10} * I269N1 =  Ideal.span {B.equivFun.symm ![-180, -16, 3]} * (J0 ^ 0*J1^ 1*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1J2_1 E269RS1 
