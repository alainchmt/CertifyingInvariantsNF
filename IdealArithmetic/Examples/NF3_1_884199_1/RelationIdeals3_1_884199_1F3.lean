import IdealArithmetic.Examples.NF3_1_884199_1.PrimesBelow3_1_884199_1F3
import IdealArithmetic.Examples.NF3_1_884199_1.ClassGroupData3_1_884199_1

set_option linter.all false

noncomputable section


noncomputable def E151RS1 : RelationCertificate Table 25 ![![151, 0, 0], ![-35, 1, 0]]
  ![-513, -132, -25] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![3775, 0, 0], ![-875, 25, 0]]
    hsu := by decide
    w := ![![-12825, -3300, -625], ![-1550, -400, -75]]
    hw := by decide
    g := ![![![-5, -10, 2], ![53, 0, 0]], ![![16, 4, -1], ![-7, 0, 0]]]
    h := ![![![-438, -317607, 28025], ![-1875, -1410600, 0]], ![![-47, -38385, 3387], ![-201, -170480, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {25} * I151N1 =  Ideal.span {B.equivFun.symm ![-513, -132, -25]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E151RS1 


noncomputable def E163RS1 : RelationCertificate Table 5 ![![163, 0, 0], ![-60, 1, 0]]
  ![64, 16, 3] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![815, 0, 0], ![-300, 5, 0]]
    hsu := by decide
    w := ![![320, 80, 15], ![-470, -115, -20]]
    hw := by decide
    g := ![![![12, -11, 2], ![-4, 0, 0]], ![![2, 5, -1], ![2, 0, 0]]]
    h := ![![![20128, -335, 0], ![54680, 1, 0]], ![![-29458, 569, -4], ![-80026, 216, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {5} * I163N1 =  Ideal.span {B.equivFun.symm ![64, 16, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E163RS1 


noncomputable def E173RS0 : RelationCertificate Table 25 ![![173, 0, 0], ![11, 1, 0]]
  ![-33, -7, -1] ![![25, 0, 0], ![-28, -3, 1]] where
    su := ![![4325, 0, 0], ![275, 25, 0]]
    hsu := by decide
    w := ![![-825, -175, -25], ![-275, -25, 0]]
    hw := by decide
    g := ![![![49, 2, -1], ![-24, 0, 0]], ![![28, 3, -1], ![24, 0, 0]]]
    h := ![![![308, 20, -2], ![-4847, 115, 0]], ![![88, -4, -3], ![-1385, 173, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N0 : Ideal.span {25} * I173N0 =  Ideal.span {B.equivFun.symm ![-33, -7, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E173RS0 


noncomputable def E173RS1 : RelationCertificate Table 125 ![![173, 0, 0], ![44, 1, 0]]
  ![52064942, 13358513, 2526030] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![21625, 0, 0], ![5500, 125, 0]]
    hsu := by decide
    w := ![![6508117750, 1669814125, 315753750], ![-21794876125, -5591999625, -1057420000]]
    hw := by decide
    g := ![![![-34209, -22, 1064], ![14657, 0, 0]], ![![-6770, -22, 219], ![3015, 0, 0]]]
    h := ![![![671690182, 16456018, 89265], ![-2639780376, -4305605, 0]], ![![-2249407017, -55109275, -298945], ![8840296703, 14419375, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {125} * I173N1 =  Ideal.span {B.equivFun.symm ![52064942, 13358513, 2526030]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E173RS1 


noncomputable def E173RS2 : RelationCertificate Table 125 ![![173, 0, 0], ![-56, 1, 0]]
  ![-4279920, -410235, 137236] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![21625, 0, 0], ![-7000, 125, 0]]
    hsu := by decide
    w := ![![-534990000, -51279375, 17154500], ![-1178802625, -78639375, 30866000]]
    hw := by decide
    g := ![![![7727436308, 1565219624, 478430797], ![-3623214738, 0, 0]], ![![-1792719235, -363121628, -110993100], ![840564340, 0, 0]]]
    h := ![![![-13876987008, 247877953, -3430], ![-42869901294, 243542, 0]], ![![-30583092729, 546292497, -7870], ![-94479743066, 536146, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N2 : Ideal.span {125} * I173N2 =  Ideal.span {B.equivFun.symm ![-4279920, -410235, 137236]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E173RS2 


noncomputable def E181RS0 : RelationCertificate Table 125 ![![181, 0, 0], ![60, 1, 0]]
  ![-61015, -6520, 2092] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![22625, 0, 0], ![7500, 125, 0]]
    hsu := by decide
    w := ![![-7626875, -815000, 261500], ![-18280625, -1311000, 497125]]
    hw := by decide
    g := ![![![2060405, 417352, 127564], ![-965992, 0, 0]], ![![863641, 174949, 53467], ![-404807, 0, 0]]]
    h := ![![![-185496715, -3869302, -38234], ![559580740, 2307482, 0]], ![![-444482545, -9271921, -91642], ![1340853240, 5530393, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N0 : Ideal.span {125} * I181N0 =  Ideal.span {B.equivFun.symm ![-61015, -6520, 2092]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E181RS0 


noncomputable def E181RS1 : RelationCertificate Table 5 ![![181, 0, 0], ![-57, 1, 0]]
  ![-3792, -973, -184] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![905, 0, 0], ![-285, 5, 0]]
    hsu := by decide
    w := ![![-18960, -4865, -920], ![26485, 6795, 1285]]
    hw := by decide
    g := ![![![8, -35, 10], ![171, 0, 0]], ![![23, 13, -4], ![-61, 0, 0]]]
    h := ![![![-470652, 8363, -7], ![-1494460, 361, 0]], ![![657677, -11653, 8], ![2088320, -397, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {5} * I181N1 =  Ideal.span {B.equivFun.symm ![-3792, -973, -184]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 5 ![![191, 0, 0], ![-67, 1, 0]]
  ![94323, 2057, -1615] ![![5, 0, 0], ![-38, -3, 1]] where
    su := ![![955, 0, 0], ![-335, 5, 0]]
    hsu := by decide
    w := ![![471615, 10285, -8075], ![-1151285, -143025, 43510]]
    hw := by decide
    g := ![![![361359, 12527915, 5256382], ![-9211513, 0, 0]], ![![-96706, -3354000, -1407252], ![2466133, 0, 0]]]
    h := ![![![30046761, -495707, 2140], ![85654284, -136785, 0]], ![![-73347073, 1210055, -5204], ![-209090458, 334222, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {5} * I191N1 =  Ideal.span {B.equivFun.symm ![94323, 2057, -1615]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 125 ![![193, 0, 0], ![-54, 1, 0]]
  ![517897, -16337, -3291] ![![125, 0, 0], ![-53, -28, 1]] where
    su := ![![24125, 0, 0], ![-6750, 125, 0]]
    hsu := by decide
    w := ![![64737125, -2042125, -411375], ![-2299625, -9139500, 1873750]]
    hw := by decide
    g := ![![![250767080, 50793762, 15525808], ![-117578831, 0, 0]], ![![-49549174, -10036353, -3067753], ![23232521, 0, 0]]]
    h := ![![![246607, 181555236, -10276989], ![871801, 661151862, 0]], ![![-7333, -5417575, 306719], ![-25868, -19727259, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {125} * I193N1 =  Ideal.span {B.equivFun.symm ![517897, -16337, -3291]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E193RS1 
