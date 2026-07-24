import IdealArithmetic.Examples.NF3_1_331240_2.PrimesBelow3_1_331240_2F3
import IdealArithmetic.Examples.NF3_1_331240_2.ClassGroupData3_1_331240_2

set_option linter.all false

noncomputable section


noncomputable def E149RS1 : RelationCertificate Table 9 ![![149, 0, 0], ![-15, 1, 0]]
  ![-10721, -632, -1166] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![1341, 0, 0], ![-135, 9, 0]]
    hsu := by decide
    w := ![![-96489, -5688, -10494], ![-171144, -10089, -18612]]
    hw := by decide
    g := ![![![-2016337, 48897138, -543413827], ![4536873, 444611323, 0]], ![![216523, -5250700, 58353163], ![-487168, -47743499, 0]]]
    h := ![![![-351589, 23456, -22], ![-3491736, 192, 0]], ![![-623644, 41595, -33], ![-6193596, 259, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {9} * I149N1 =  Ideal.span {B.equivFun.symm ![-10721, -632, -1166]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E149RS1 


noncomputable def E151RS1 : RelationCertificate Table 18 ![![151, 0, 0], ![42, 1, 0]]
  ![-1148, -68, -125] ![![18, 0, 0], ![4, 1, 0]] where
    su := ![![2718, 0, 0], ![756, 18, 0]]
    hsu := by decide
    w := ![![-20664, -1224, -2250], ![-18342, -1080, -1998]]
    hw := by decide
    g := ![![![-8389, 715332, -7891784], ![37879, 12913824, 0]], ![![-24667974, 2096778046, -23132395445], ![111005910, 37853010727, 0]]]
    h := ![![![-4928, -135, -6], ![17690, 71, 0]], ![![-4397, -126, -7], ![15784, 86, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {18} * I151N1 =  Ideal.span {B.equivFun.symm ![-1148, -68, -125]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E151RS1 


noncomputable def E157RS0 : RelationCertificate Table 18 ![![157, 0, 0], ![76, 1, 0]]
  ![-551258, -32498, -59951] ![![18, 0, 0], ![4, 1, 0]] where
    su := ![![2826, 0, 0], ![1368, 18, 0]]
    hsu := by decide
    w := ![![-9922644, -584964, -1079118], ![-8799642, -518760, -956988]]
    hw := by decide
    g := ![![![-31702, 2752801, -30369875], ![145891, 49696082, 0]], ![![-42441363816, 3607515949646, -39799389197376], ![190986138588, 65126273232031, 0]]]
    h := ![![![99004814, 1284170, -3227], ![-204530356, 40608, 0]], ![![87799859, 1138767, -2872], ![-181382457, 36158, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N0 : Ideal.span {18} * I157N0 =  Ideal.span {B.equivFun.symm ![-551258, -32498, -59951]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E157RS0 


noncomputable def E157RS1 : RelationCertificate Table 18 ![![157, 0, 0], ![-46, 1, 0]]
  ![15958, 2458, -2459] ![![18, 0, 0], ![4, 1, 0]] where
    su := ![![2826, 0, 0], ![-828, 18, 0]]
    hsu := by decide
    w := ![![287244, 44244, -44262], ![-206658, 13500, 2448]]
    hw := by decide
    g := ![![![1059904, 51751, 127746], ![238425, -10990, 0]], ![![-229786, -11173, -28211], ![-51682, 3227, 0]]]
    h := ![![![15813674, -370494, 5751], ![53972410, -82306, 0]], ![![-11384953, 266761, -4153], ![-38857090, 59287, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {18} * I157N1 =  Ideal.span {B.equivFun.symm ![15958, 2458, -2459]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E157RS1 


noncomputable def E157RS2 : RelationCertificate Table 18 ![![157, 0, 0], ![-31, 1, 0]]
  ![-532, -28, 47] ![![18, 0, 0], ![4, 1, 0]] where
    su := ![![2826, 0, 0], ![-558, 18, 0]]
    hsu := by decide
    w := ![![-9576, -504, 846], ![3042, -504, 162]]
    hw := by decide
    g := ![![![517, -233, 2902], ![119, -4652, 0]], ![![649, -60762, 670298], ![-3217, -1096863, 0]]]
    h := ![![![-9132, 328, -10], ![-46232, 147, 0]], ![![2921, -68, -8], ![14788, 115, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N2 : Ideal.span {18} * I157N2 =  Ideal.span {B.equivFun.symm ![-532, -28, 47]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E157RS2 
