import IdealArithmetic.Examples.NF3_1_936684_4.PrimesBelow3_1_936684_4F4
import IdealArithmetic.Examples.NF3_1_936684_4.ClassGroupData3_1_936684_4

set_option linter.all false

noncomputable section


noncomputable def E199RS0 : RelationCertificate Table 10 ![![199, 0, 0], ![98, 1, 0]]
  ![-40, -8, 1] ![![10, 0, 0], ![-2, 1, 0]] where
    su := ![![1990, 0, 0], ![980, 10, 0]]
    hsu := by decide
    w := ![![-400, -80, 10], ![430, 60, -10]]
    hw := by decide
    g := ![![![11, 227, -115], ![23, 1148, 0]], ![![178, 9052, -4570], ![876, 45699, 0]]]
    h := ![![![-18176, -284, -1], ![36908, 200, 0]], ![![19255, 197, 0], ![-39099, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N0 : Ideal.span {10} * I199N0 =  Ideal.span {B.equivFun.symm ![-40, -8, 1]} * (J0 ^ 1*J1^ 0*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0J2_1 E199RS0 


noncomputable def E199RS1 : RelationCertificate Table 50 ![![199, 0, 0], ![-78, 1, 0]]
  ![-150, -52, -5] ![![50, 0, 0], ![-506, -25, 9]] where
    su := ![![9950, 0, 0], ![-3900, 50, 0]]
    hsu := by decide
    w := ![![-7500, -2600, -250], ![-44150, -14500, -1300]]
    hw := by decide
    g := ![![![408, 14, -7], ![47, 0, 0]], ![![26, -183, -62], ![616, 99, 0]]]
    h := ![![![-6102, 154, -1], ![-15566, 194, 0]], ![![-36481, 534, -1], ![-93062, 173, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {50} * I199N1 =  Ideal.span {B.equivFun.symm ![-150, -52, -5]} * (J0 ^ 2*J1^ 2*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2J2_1 E199RS1 


noncomputable def E199RS2 : RelationCertificate Table 10 ![![199, 0, 0], ![-20, 1, 0]]
  ![-110, -34, -3] ![![10, 0, 0], ![2, 1, 0]] where
    su := ![![1990, 0, 0], ![-200, 10, 0]]
    hsu := by decide
    w := ![![-1100, -340, -30], ![-1270, -430, -40]]
    hw := by decide
    g := ![![![126917, -6598905, -3331181], ![-634497, 33311803, 0]], ![![-13395, 696365, 351531], ![66960, -3515309, 0]]]
    h := ![![![-130, 26, -1], ![-1288, 196, 0]], ![![-113, 25, -1], ![-1118, 195, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N2 : Ideal.span {10} * I199N2 =  Ideal.span {B.equivFun.symm ![-110, -34, -3]} * (J0 ^ 0*J1^ 1*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1J2_1 E199RS2 


noncomputable def E211RS1 : RelationCertificate Table 50 ![![211, 0, 0], ![47, 1, 0]]
  ![650, 58, -11] ![![50, 0, 0], ![-22, 1, 0]] where
    su := ![![10550, 0, 0], ![2350, 50, 0]]
    hsu := by decide
    w := ![![32500, 2900, -550], ![-18150, -1550, 300]]
    hw := by decide
    g := ![![![-3856143, -523034248, 23782251], ![-8763947, -1189112557, 0]], ![![-840674, -114026421, 5184756], ![-1910619, -259237802, 0]]]
    h := ![![![1238, -18, -1], ![-5544, 200, 0]], ![![-778, -18, 0], ![3485, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {50} * I211N1 =  Ideal.span {B.equivFun.symm ![650, 58, -11]} * (J0 ^ 2*J1^ 0*J2^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0J2_1 E211RS1 


noncomputable def E227RS1 : RelationCertificate Table 5 ![![227, 0, 0], ![-106, 1, 0]]
  ![-15, -2, 0] ![![5, 0, 0], ![-54, -5, 1]] where
    su := ![![1135, 0, 0], ![-530, 5, 0]]
    hsu := by decide
    w := ![![-75, -10, 0], ![110, 15, -5]]
    hw := by decide
    g := ![![![33, 7, -1], ![1, 0, 0]], ![![10, -1, 0], ![2, 0, 0]]]
    h := ![![![-107, 107, -1], ![-229, 227, 0]], ![![270, 103, -1], ![578, 226, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {5} * I227N1 =  Ideal.span {B.equivFun.symm ![-15, -2, 0]} * (J0 ^ 1*J1^ 1*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1J2_0 E227RS1 


noncomputable def E229RS1 : RelationCertificate Table 5 ![![229, 0, 0], ![111, 1, 0]]
  ![-45, -7, 1] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![1145, 0, 0], ![555, 5, 0]]
    hsu := by decide
    w := ![![-225, -35, 5], ![260, 25, -5]]
    hw := by decide
    g := ![![![148371, -2151310, -1112746], ![-370913, 5563728, 0]], ![![72657, -1053523, -544925], ![-181637, 2724624, 0]]]
    h := ![![![-8157, -185, -1], ![16828, 230, 0]], ![![9046, 82, 0], ![-18662, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {5} * I229N1 =  Ideal.span {B.equivFun.symm ![-45, -7, 1]} * (J0 ^ 0*J1^ 1*J2^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1J2_0 E229RS1 


noncomputable def E233RS1 : RelationCertificate Table 10 ![![233, 0, 0], ![-71, 1, 0]]
  ![20, 3, 0] ![![10, 0, 0], ![-54, 0, 1]] where
    su := ![![2330, 0, 0], ![-710, 10, 0]]
    hsu := by decide
    w := ![![200, 30, 0], ![-30, 90, 20]]
    hw := by decide
    g := ![![![13, -6, 0], ![9, 0, 0]], ![![50, 2, -1], ![7, 0, 0]]]
    h := ![![![16970, -239, 0], ![55690, 0, 0]], ![![-2510, 107, -1], ![-8237, 235, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {10} * I233N1 =  Ideal.span {B.equivFun.symm ![20, 3, 0]} * (J0 ^ 1*J1^ 1*J2^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1J2_2 E233RS1 
