import IdealArithmetic.Examples.NF3_1_283015_1.PrimesBelow3_1_283015_1F3
import IdealArithmetic.Examples.NF3_1_283015_1.ClassGroupData3_1_283015_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 3 ![![139, 0, 0], ![26, 1, 0]]
  ![2143, 74, -222] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![417, 0, 0], ![78, 3, 0]]
    hsu := by decide
    w := ![![6429, 222, -666], ![21978, 3549, 666]]
    hw := by decide
    g := ![![![3667369, -210212, 279054], ![-70070, 0, 0]], ![![487232, -27928, 37074], ![-9309, 0, 0]]]
    h := ![![![110039, 4435, 66], ![-588203, -1044, 0]], ![![376358, 15224, 249], ![-2011786, -3821, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {3} * I139N1 =  Ideal.span {B.equivFun.symm ![2143, 74, -222]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS1 
