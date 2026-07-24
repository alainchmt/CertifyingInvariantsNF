import IdealArithmetic.Examples.NF3_1_408807_1.PrimesBelow3_1_408807_1F3
import IdealArithmetic.Examples.NF3_1_408807_1.ClassGroupData3_1_408807_1

set_option linter.all false

noncomputable section


noncomputable def E151RS1 : RelationCertificate Table 25 ![![151, 0, 0], ![5, 1, 0]]
  ![-151, -10, -6] ![![25, 0, 0], ![-5, 1, 0]] where
    su := ![![3775, 0, 0], ![125, 25, 0]]
    hsu := by decide
    w := ![![-3775, -250, -150], ![125, 25, 0]]
    hw := by decide
    g := ![![![-287156, -37330774, 22432923], ![-1435775, -186941027, 0]], ![![-10870, -1413331, 849303], ![-54349, -7077525, 0]]]
    h := ![![![-17736, -3552, -3], ![535597, 149, 0]], ![![580, 116, 0], ![-17515, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {25} * I151N1 =  Ideal.span {B.equivFun.symm ![-151, -10, -6]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 605 ![![157, 0, 0], ![7, 1, 0]]
  ![208, 5, -17] ![![605, 0, 0], ![250, 1, 0]] where
    su := ![![94985, 0, 0], ![4235, 605, 0]]
    hsu := by decide
    w := ![![125840, 3025, -10285], ![50215, 1815, -4235]]
    hw := by decide
    g := ![![![903590379, -1548844616974, -18586178776], ![-2186688715, 3748212719832, 0]], ![![39328117, -67412557771, -808952581], ![-95174043, 163138770502, 0]]]
    h := ![![![396, 52, -2], ![-8852, 99, 0]], ![![156, 20, -1], ![-3487, 50, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {605} * I157N1 =  Ideal.span {B.equivFun.symm ![208, 5, -17]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E157RS1 


noncomputable def E163RS0 : RelationCertificate Table 5 ![![163, 0, 0], ![67, 1, 0]]
  ![109, 5, 4] ![![5, 0, 0], ![0, 1, 0]] where
    su := ![![815, 0, 0], ![335, 5, 0]]
    hsu := by decide
    w := ![![545, 25, 20], ![420, 25, 15]]
    hw := by decide
    g := ![![![4, 0, -1], ![3, 0, 0]], ![![1, 0, 14], ![2, -24, 0]]]
    h := ![![![2224, -12, -2], ![-5409, 110, 0]], ![![1634, 24, 0], ![-3974, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N0 : Ideal.span {5} * I163N0 =  Ideal.span {B.equivFun.symm ![109, 5, 4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E163RS0 


noncomputable def E163RS1 : RelationCertificate Table 5 ![![163, 0, 0], ![-46, 1, 0]]
  ![1, 0, 1] ![![5, 0, 0], ![0, 1, 0]] where
    su := ![![815, 0, 0], ![-230, 5, 0]]
    hsu := by decide
    w := ![![5, 0, 5], ![105, -20, 0]]
    hw := by decide
    g := ![![![16, 1, 2], ![2, -2, 0]], ![![-4, -1, 1], ![3, -2, 0]]]
    h := ![![![81, 29, -2], ![287, 109, 0]], ![![413, -9, 0], ![1463, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {5} * I163N1 =  Ideal.span {B.equivFun.symm ![1, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E163RS1 


noncomputable def E163RS2 : RelationCertificate Table 5 ![![163, 0, 0], ![-21, 1, 0]]
  ![16, 0, 1] ![![5, 0, 0], ![0, 1, 0]] where
    su := ![![815, 0, 0], ![-105, 5, 0]]
    hsu := by decide
    w := ![![80, 0, 5], ![105, -5, 0]]
    hw := by decide
    g := ![![![1, 1, 124634], ![2, -207723, 0]], ![![0, -1, -12219], ![4, 20365, 0]]]
    h := ![![![1702, -67, -2], ![13210, 109, 0]], ![![2247, -107, 0], ![17440, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N2 : Ideal.span {5} * I163N2 =  Ideal.span {B.equivFun.symm ![16, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E163RS2 


noncomputable def E173RS1 : RelationCertificate Table 5 ![![173, 0, 0], ![21, 1, 0]]
  ![26, 0, 1] ![![5, 0, 0], ![0, 1, 0]] where
    su := ![![865, 0, 0], ![105, 5, 0]]
    hsu := by decide
    w := ![![130, 0, 5], ![105, 5, 0]]
    hw := by decide
    g := ![![![1, 1, 439], ![2, -732, 0]], ![![0, 0, 54], ![1, -90, 0]]]
    h := ![![![64, -4, -1], ![-526, 58, 0]], ![![42, 2, 0], ![-345, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {5} * I173N1 =  Ideal.span {B.equivFun.symm ![26, 0, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E173RS1 


noncomputable def E179RS0 : RelationCertificate Table 11 ![![179, 0, 0], ![9, 1, 0]]
  ![-107, -4, -4] ![![11, 0, 0], ![-3, 1, 0]] where
    su := ![![1969, 0, 0], ![99, 11, 0]]
    hsu := by decide
    w := ![![-1177, -44, -44], ![-99, -11, 0]]
    hw := by decide
    g := ![![![225080, 9753313, -9828340], ![825289, 36037248, 0]], ![![11904, 515800, -519768], ![43647, 1905816, 0]]]
    h := ![![![-109, -18, -2], ![2156, 118, 0]], ![![-9, -10, -3], ![178, 179, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N0 : Ideal.span {11} * I179N0 =  Ideal.span {B.equivFun.symm ![-107, -4, -4]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E179RS0 


noncomputable def E179RS1 : RelationCertificate Table 25 ![![179, 0, 0], ![75, 1, 0]]
  ![-8, -5, 2] ![![25, 0, 0], ![-5, 1, 0]] where
    su := ![![4475, 0, 0], ![1875, 25, 0]]
    hsu := by decide
    w := ![![-200, -125, 50], ![250, -25, -25]]
    hw := by decide
    g := ![![![37, 5592, -3361], ![226, 28006, 0]], ![![15, 2381, -1431], ![93, 11924, 0]]]
    h := ![![![-202, -53, -2], ![482, 120, 0]], ![![140, -48, -2], ![-334, 119, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {25} * I179N1 =  Ideal.span {B.equivFun.symm ![-8, -5, 2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E179RS1 


noncomputable def E179RS2 : RelationCertificate Table 605 ![![179, 0, 0], ![-84, 1, 0]]
  ![-764, -30, -19] ![![605, 0, 0], ![250, 1, 0]] where
    su := ![![108295, 0, 0], ![-50820, 605, 0]]
    hsu := by decide
    w := ![![-462220, -18150, -11495], ![-192995, -7865, -4840]]
    hw := by decide
    g := ![![![779640817, -1336382603021, -16036628659], ![-1886730778, 3234053446234, 0]], ![![-357338849, 612514333395, 7350189153], ![864760015, -1482288145856, 0]]]
    h := ![![![-46973404, 642588, -2978], ![-100098078, 177681, 0]], ![![-19613021, 268375, -1246], ![-41794410, 74342, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N2 : Ideal.span {605} * I179N2 =  Ideal.span {B.equivFun.symm ![-764, -30, -19]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E179RS2 
