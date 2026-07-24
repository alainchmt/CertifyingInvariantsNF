import IdealArithmetic.Examples.NF3_1_936091_2.PrimesBelow3_1_936091_2F5
import IdealArithmetic.Examples.NF3_1_936091_2.ClassGroupData3_1_936091_2

set_option linter.all false

noncomputable section


noncomputable def E263RS1 : RelationCertificate Table 2 ![![263, 0, 0], ![-85, 1, 0]]
  ![29, 1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![526, 0, 0], ![-170, 2, 0]]
    hsu := by decide
    w := ![![58, 2, 2], ![100, -2, 4]]
    hw := by decide
    g := ![![![-307935, 246354, 769859], ![123177, -307943, 0]], ![![97741, -78195, -244358], ![-39096, 97743, 0]]]
    h := ![![![-10547, -461935, 27827], ![1806, -1463700, 0]], ![![-18205, -796878, 48004], ![3083, -2525010, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R263N1 : Ideal.span {2} * I263N1 =  Ideal.span {B.equivFun.symm ![29, 1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E263RS1 


noncomputable def E269RS1 : RelationCertificate Table 9 ![![269, 0, 0], ![112, 1, 0]]
  ![3, 0, 2] ![![9, 0, 0], ![1, 1, 0]] where
    su := ![![2421, 0, 0], ![1008, 9, 0]]
    hsu := by decide
    w := ![![27, 0, 18], ![207, -63, 0]]
    hw := by decide
    g := ![![![-3922, 5895, 9866], ![225, -17756, 0]], ![![-1619, 2434, 4074], ![95, -7332, 0]]]
    h := ![![![12827, -790075, -34652], ![2483, 1864278, 0]], ![![98667, -6064413, -265980], ![18554, 14309724, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R269N1 : Ideal.span {9} * I269N1 =  Ideal.span {B.equivFun.symm ![3, 0, 2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E269RS1 


noncomputable def E271RS1 : RelationCertificate Table 3 ![![271, 0, 0], ![45, 1, 0]]
  ![1222287, 28758, 36191] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![813, 0, 0], ![135, 3, 0]]
    hsu := by decide
    w := ![![3666861, 86274, 108573], ![4856253, 114258, 143790]]
    hw := by decide
    g := ![![![-3556, 4380, 7398], ![277, -4336, 0]], ![![-526, 693, 1217], ![59, -712, 0]]]
    h := ![![![1845207720, -43925942645, -4672915849], ![144311615, 253272046254, 0]], ![![2443723812, -58173868809, -6188634260], ![191120859, 335423986478, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R271N1 : Ideal.span {3} * I271N1 =  Ideal.span {B.equivFun.symm ![1222287, 28758, 36191]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E271RS1 
