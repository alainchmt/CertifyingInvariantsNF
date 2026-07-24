import IdealArithmetic.Examples.NF3_1_905324_3.PrimesBelow3_1_905324_3F5
import IdealArithmetic.Examples.NF3_1_905324_3.ClassGroupData3_1_905324_3

set_option linter.all false

noncomputable section


noncomputable def E263RS1 : RelationCertificate Table 2873 ![![263, 0, 0], ![-110, 1, 0]]
  ![827, 104, 47] ![![2873, 0, 0], ![-858, 1, 0]] where
    su := ![![755599, 0, 0], ![-316030, 2873, 0]]
    hsu := by decide
    w := ![![2375971, 298792, 135031], ![-701012, -89063, -40222]]
    hw := by decide
    g := ![![![2005, 14667508, -17095], ![6714, 49113936, 0]], ![![-14, -6046326, 7047], ![-47, -20246031, 0]]]
    h := ![![![29819, -251, 0], ![71287, 47, 0]], ![![-8688, 183, -1], ![-20770, 249, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {2873} * I263N1 =  Ideal.span {B.equivFun.symm ![827, 104, 47]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E263RS1 


noncomputable def E269RS1 : RelationCertificate Table 221 ![![269, 0, 0], ![-100, 1, 0]]
  ![199, 13, -9] ![![221, 0, 0], ![26, 1, 0]] where
    su := ![![59449, 0, 0], ![-22100, 221, 0]]
    hsu := by decide
    w := ![![43979, 2873, -1989], ![3536, 663, -221]]
    hw := by decide
    g := ![![![13, -54315, -2089], ![-88, 461683, 0]], ![![-14, 19890, 765], ![111, -169070, 0]]]
    h := ![![![5223471, -57538, 53], ![14051135, -14266, 0]], ![![419864, -4599, 4], ![1129434, -1077, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R269N1 : Ideal.span {221} * I269N1 =  Ideal.span {B.equivFun.symm ![199, 13, -9]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E269RS1 
