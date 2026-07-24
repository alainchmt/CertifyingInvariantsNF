import IdealArithmetic.Examples.NF3_1_538412_3.PrimesBelow3_1_538412_3F4
import IdealArithmetic.Examples.NF3_1_538412_3.ClassGroupData3_1_538412_3

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 25 ![![199, 0, 0], ![82, 1, 0]]
  ![-4382, 1196, -535] ![![25, 0, 0], ![4, 1, 0]] where
    su := ![![4975, 0, 0], ![2050, 25, 0]]
    hsu := by decide
    w := ![![-109550, 29900, -13375], ![-99100, -7875, 8750]]
    hw := by decide
    g := ![![![51124, 56439, 231987], ![10454, -555200, 400]], ![![28170, 24156, 96428], ![5480, -229028, 165]]]
    h := ![![![3435478, -148462258, -18557365], ![669738, 369291510, 0]], ![![3044364, -131560438, -16444680], ![593487, 327249167, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {25} * I199N1 =  Ideal.span {B.equivFun.symm ![-4382, 1196, -535]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E199RS1 
