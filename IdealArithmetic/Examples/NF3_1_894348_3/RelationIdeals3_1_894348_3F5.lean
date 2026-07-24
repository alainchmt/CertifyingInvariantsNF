import IdealArithmetic.Examples.NF3_1_894348_3.PrimesBelow3_1_894348_3F5
import IdealArithmetic.Examples.NF3_1_894348_3.ClassGroupData3_1_894348_3

set_option linter.all false

noncomputable section


noncomputable def E263RS1 : RelationCertificate Table 11 ![![263, 0, 0], ![57, 1, 0]]
  ![23, 3, -3] ![![11, 0, 0], ![-4, 1, 0]] where
    su := ![![2893, 0, 0], ![627, 11, 0]]
    hsu := by decide
    w := ![![253, 33, -33], ![-638, 11, 33]]
    hw := by decide
    g := ![![![-9, -905, 1599], ![-74, -2511, 0]], ![![1, -206, 363], ![-10, -570, 0]]]
    h := ![![![157, -46, -6], ![-724, 225, 0]], ![![-728, -21, -1], ![3358, 38, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {11} * I263N1 =  Ideal.span {B.equivFun.symm ![23, 3, -3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E263RS1 
