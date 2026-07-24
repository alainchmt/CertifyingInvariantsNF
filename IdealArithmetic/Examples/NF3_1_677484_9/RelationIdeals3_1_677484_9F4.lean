import IdealArithmetic.Examples.NF3_1_677484_9.PrimesBelow3_1_677484_9F4
import IdealArithmetic.Examples.NF3_1_677484_9.ClassGroupData3_1_677484_9

set_option linter.all false

noncomputable section


noncomputable def E197RS0 : RelationCertificate Table 121 ![![197, 0, 0], ![-92, 1, 0]]
  ![-12328457, -2426541, -834092] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![23837, 0, 0], ![-11132, 121, 0]]
    hsu := by decide
    w := ![![-1491743297, -293611461, -100925132], ![142329517, 28013920, 9629422]]
    hw := by decide
    g := ![![![-12792599, -6828569180, 1412898712], ![-53368430, -28493456355, 0]], ![![5946403, 3174085400, -656749762], ![24807039, 13244453040, 0]]]
    h := ![![![-147512729, 1760510, -15328], ![-315735643, 364254, 0]], ![![14074589, -167937, 1460], ![30125193, -34673, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N0 : Ideal.span {121} * I197N0 =  Ideal.span {B.equivFun.symm ![-12328457, -2426541, -834092]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E197RS0 


noncomputable def E197RS2 : RelationCertificate Table 11 ![![197, 0, 0], ![-24, 1, 0]]
  ![29, 3, 1] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![2167, 0, 0], ![-264, 11, 0]]
    hsu := by decide
    w := ![![319, 33, 11], ![374, 77, 22]]
    hw := by decide
    g := ![![![-73, 2787, 4213], ![235, -7724, 0]], ![![6, -334, -504], ![-21, 924, 0]]]
    h := ![![![7897, -325, -1], ![64820, 33, 0]], ![![9290, -379, -2], ![76254, 66, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N2 : Ideal.span {11} * I197N2 =  Ideal.span {B.equivFun.symm ![29, 3, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E197RS2 


noncomputable def E227RS1 : RelationCertificate Table 121 ![![227, 0, 0], ![-16, 1, 0]]
  ![22307627, 4390685, 1509241] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![27467, 0, 0], ![-1936, 121, 0]]
    hsu := by decide
    w := ![![2699222867, 531272885, 182618161], ![-257537005, -50689562, -17423879]]
    hw := by decide
    g := ![![![-780, 116855, -24137], ![1249, 488244, 0]], ![![155, -7876, 1624], ![-19, -32936, 0]]]
    h := ![![![122481545, -7664152, 19601], ![1736312693, -490031, 0]], ![![-11686135, 731255, -1873], ![-165664015, 46862, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {121} * I227N1 =  Ideal.span {B.equivFun.symm ![22307627, 4390685, 1509241]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E227RS1 
