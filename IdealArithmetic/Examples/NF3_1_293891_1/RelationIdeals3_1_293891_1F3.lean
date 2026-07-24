import IdealArithmetic.Examples.NF3_1_293891_1.PrimesBelow3_1_293891_1F3
import IdealArithmetic.Examples.NF3_1_293891_1.ClassGroupData3_1_293891_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 32 ![![139, 0, 0], ![-27, 1, 0]]
  ![1837, 151, 55] ![![32, 0, 0], ![-1, 1, 0]] where
    su := ![![4448, 0, 0], ![-864, 32, 0]]
    hsu := by decide
    w := ![![58784, 4832, 1760], ![3168, 256, 96]]
    hw := by decide
    g := ![![![3, -337, 335], ![11, -10707, 0]], ![![0, 63, -63], ![8, 2013, 0]]]
    h := ![![![1726657, -66044, 78], ![8889018, -10787, 0]], ![![93087, -3555, 4], ![479222, -553, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {32} * I139N1 =  Ideal.span {B.equivFun.symm ![1837, 151, 55]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E139RS1 
