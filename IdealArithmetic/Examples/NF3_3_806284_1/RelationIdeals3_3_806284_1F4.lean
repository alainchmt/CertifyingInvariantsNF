import IdealArithmetic.Examples.NF3_3_806284_1.PrimesBelow3_3_806284_1F4
import IdealArithmetic.Examples.NF3_3_806284_1.ClassGroupData3_3_806284_1

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 2 ![![199, 0, 0], ![-61, 1, 0]]
  ![133, 3, -3] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![398, 0, 0], ![-122, 2, 0]]
    hsu := by decide
    w := ![![266, 6, -6], ![-176, -14, 6]]
    hw := by decide
    g := ![![![84, 41, 12], ![65, 0, 0]], ![![-22, -11, -3], ![-15, 0, 0]]]
    h := ![![![7721, -97, -1], ![25186, 98, 0]], ![![-5038, 113, -1], ![-16434, 101, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {2} * I199N1 =  Ideal.span {B.equivFun.symm ![133, 3, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E199RS1 
