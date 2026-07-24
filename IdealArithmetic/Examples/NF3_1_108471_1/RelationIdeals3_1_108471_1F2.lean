import IdealArithmetic.Examples.NF3_1_108471_1.PrimesBelow3_1_108471_1F2
import IdealArithmetic.Examples.NF3_1_108471_1.ClassGroupData3_1_108471_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 5 ![![89, 0, 0], ![-33, 1, 0]]
  ![1865917, -571572, 231927] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![445, 0, 0], ![-165, 5, 0]]
    hsu := by decide
    w := ![![9329585, -2857860, 1159635], ![41603255, -12744005, 5171140]]
    hw := by decide
    g := ![![![1779, -1993, -559], ![-2854, 0, 0]], ![![-434, 570, 194], ![695, 0, 0]]]
    h := ![![![28072328, -931133, 13273], ![75653675, -189874, 0]], ![![125182286, -4152313, 59207], ![337360691, -847039, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {5} * I89N1 =  Ideal.span {B.equivFun.symm ![1865917, -571572, 231927]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E89RS2 : RelationCertificate Table 5 ![![89, 0, 0], ![-2, 1, 0]]
  ![52954, -16221, 6582] ![![5, 0, 0], ![-10, -2, 1]] where
    su := ![![445, 0, 0], ![-10, 5, 0]]
    hsu := by decide
    w := ![![264770, -81105, 32910], ![1180685, -361670, 146755]]
    hw := by decide
    g := ![![![-520, 297, -57], ![912, 0, 0]], ![![-7, 0, -7], ![23, 0, 0]]]
    h := ![![![500286, -250503, 668], ![22236250, -10574, 0]], ![![2230919, -1117081, 2999], ![99157827, -47512, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N2 : Ideal.span {5} * I89N2 =  Ideal.span {B.equivFun.symm ![52954, -16221, 6582]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS2 
