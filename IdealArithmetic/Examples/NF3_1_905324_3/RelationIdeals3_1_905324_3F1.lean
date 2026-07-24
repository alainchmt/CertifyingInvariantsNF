import IdealArithmetic.Examples.NF3_1_905324_3.PrimesBelow3_1_905324_3F1
import IdealArithmetic.Examples.NF3_1_905324_3.ClassGroupData3_1_905324_3

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 48841 ![![37, 0, 0], ![-7, 1, 0]]
  ![-11449, 728, 329] ![![48841, 0, 0], ![13507, 1, 0]] where
    su := ![![1807117, 0, 0], ![-341887, 48841, 0]]
    hsu := by decide
    w := ![![-559180609, 35556248, 16068689], ![-154581765, 9817041, 4444531]]
    hw := by decide
    g := ![![![-109744252056, 20864019734309183, 1544681997663], ![396832680437, -75443813447858702, 0]], ![![17890277258, -3401209866266382, -251810903057], ![-64690829315, 12298696316206944, 0]]]
    h := ![![![-42135, 6169, -16], ![-221078, 921, 0]], ![![-11645, 1709, -5], ![-61100, 276, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {48841} * I37N1 =  Ideal.span {B.equivFun.symm ![-11449, 728, 329]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 13 ![![41, 0, 0], ![-15, 1, 0]]
  ![601, 78, 16] ![![13, 0, 0], ![0, 1, 0]] where
    su := ![![533, 0, 0], ![-195, 13, 0]]
    hsu := by decide
    w := ![![7813, 1014, 208], ![2912, 377, 78]]
    hw := by decide
    g := ![![![1, -2, 132108], ![4, -1717400, 0]], ![![1, 0, -45279], ![7, 588625, 0]]]
    h := ![![![3596, -246, 1], ![9789, -25, 0]], ![![1354, -87, 0], ![3686, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {13} * I41N1 =  Ideal.span {B.equivFun.symm ![601, 78, 16]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E41RS1 


noncomputable def E53RS1 : RelationCertificate Table 221 ![![53, 0, 0], ![-19, 1, 0]]
  ![27, -26, 1] ![![221, 0, 0], ![26, 1, 0]] where
    su := ![![11713, 0, 0], ![-4199, 221, 0]]
    hsu := by decide
    w := ![![5967, -5746, 221], ![884, -663, 0]]
    hw := by decide
    g := ![![![-977167, 1860977599, 71577507], ![8305917, -15818629050, 0]], ![![325705, -620325867, -23859169], ![-2768492, 5272876350, 0]]]
    h := ![![![207, -11, 0], ![576, 1, 0]], ![![56, -3, 0], ![156, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {221} * I53N1 =  Ideal.span {B.equivFun.symm ![27, -26, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 2873 ![![59, 0, 0], ![-6, 1, 0]]
  ![-5003, -650, -128] ![![2873, 0, 0], ![-858, 1, 0]] where
    su := ![![169507, 0, 0], ![-17238, 2873, 0]]
    hsu := by decide
    w := ![![-14373619, -1867450, -367744], ![4269278, 554489, 109174]]
    hw := by decide
    g := ![![![-249200233, -2611173994134, 3043326672], ![-834443204, -8743477528660, 0]], ![![4969186, 52066408037, -60683466], ![16639244, 174343597820, 0]]]
    h := ![![![-6013, 988, -4], ![-58294, 108, 0]], ![![1790, -293, 1], ![17354, -21, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {2873} * I59N1 =  Ideal.span {B.equivFun.symm ![-5003, -650, -128]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 289 ![![61, 0, 0], ![9, 1, 0]]
  ![-409, -45, -12] ![![289, 0, 0], ![-76, 1, 0]] where
    su := ![![17629, 0, 0], ![2601, 289, 0]]
    hsu := by decide
    w := ![![-118201, -13005, -3468], ![28900, 3179, 867]]
    hw := by decide
    g := ![![![-3367, -4019367, 52887], ![-12804, -15284340, 0]], ![![-329537, -387198944, 5094780], ![-1253108, -1472391420, 0]]]
    h := ![![![-891817, -101609, -280], ![6044492, 17068, 0]], ![![218038, 24838, 68], ![-1477802, -4145, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {289} * I61N1 =  Ideal.span {B.equivFun.symm ![-409, -45, -12]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E61RS1 


noncomputable def E73RS1 : RelationCertificate Table 2873 ![![73, 0, 0], ![-2, 1, 0]]
  ![12225, 1586, 330] ![![2873, 0, 0], ![-858, 1, 0]] where
    su := ![![209729, 0, 0], ![-5746, 2873, 0]]
    hsu := by decide
    w := ![![35122425, 4556578, 948090], ![-10428990, -1353183, -281554]]
    hw := by decide
    g := ![![![3131, 27371055, -31901], ![10485, 91651575, 0]], ![![508, -595452, 694], ![1701, -1993860, 0]]]
    h := ![![![72122179, -36087317, 13171], ![2632453421, -961153, 0]], ![![-21415418, 10715499, -3912], ![-781660942, 285478, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {2873} * I73N1 =  Ideal.span {B.equivFun.symm ![12225, 1586, 330]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E73RS1 
