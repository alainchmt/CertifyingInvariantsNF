import IdealArithmetic.Examples.NF3_1_119660_3.PrimesBelow3_1_119660_3F2
import IdealArithmetic.Examples.NF3_1_119660_3.ClassGroupData3_1_119660_3

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 9 ![![97, 0, 0], ![-31, 1, 0]]
  ![17, 6, 1] ![![9, 0, 0], ![3, 1, 0]] where
    su := ![![873, 0, 0], ![-279, 9, 0]]
    hsu := by decide
    w := ![![153, 54, 9], ![117, 27, 9]]
    hw := by decide
    g := ![![![-8, 191, 65], ![23, -582, 0]], ![![2, -62, -21], ![-5, 188, 0]]]
    h := ![![![5313, -171, 0], ![16624, 1, 0]], ![![4103, -132, 0], ![12838, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {9} * I97N1 =  Ideal.span {B.equivFun.symm ![17, 6, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E97RS1 
