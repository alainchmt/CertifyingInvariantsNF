import IdealArithmetic.Examples.NF3_1_960204_2.PrimesBelow3_1_960204_2F1
import IdealArithmetic.Examples.NF3_1_960204_2.ClassGroupData3_1_960204_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 33 ![![37, 0, 0], ![14, 1, 0]]
  ![-1935, -3, -46] ![![33, 0, 0], ![29, 0, 1]] where
    su := ![![1221, 0, 0], ![462, 33, 0]]
    hsu := by decide
    w := ![![-63855, -99, -1518], ![-58476, -99, -1386]]
    hw := by decide
    g := ![![![-702611, 317436, -5704], ![-617573, 805800, 0]], ![![-40855535, 18458925, -331633], ![-35913385, 46857271, 0]]]
    h := ![![![503225, -6601892, -1523440], ![11987, 18789078, 0]], ![![460824, -6045656, -1395084], ![10983, 17206022, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {33} * I37N1 =  Ideal.span {B.equivFun.symm ![-1935, -3, -46]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 363 ![![43, 0, 0], ![3, 1, 0]]
  ![-654, 609, -67] ![![363, 0, 0], ![62, 0, 1]] where
    su := ![![15609, 0, 0], ![1089, 363, 0]]
    hsu := by decide
    w := ![![-237402, 221067, -24321], ![-12705, 11979, -1452]]
    hw := by decide
    g := ![![![4388, 1925, 85], ![856, -34950, 0]], ![![8644930, 3489126, 170386], ![1477203, -63327638, 0]]]
    h := ![![![7086060, -14198866, -21292594], ![164197, 305193825, 0]], ![![379369, -760175, -1139956], ![8822, 16339368, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {363} * I43N1 =  Ideal.span {B.equivFun.symm ![-654, 609, -67]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 11 ![![53, 0, 0], ![-2, 1, 0]]
  ![21878, 36, 519] ![![11, 0, 0], ![0, 1, 0]] where
    su := ![![583, 0, 0], ![-22, 11, 0]]
    hsu := by decide
    w := ![![240658, 396, 5709], ![26433, 44, 627]]
    hw := by decide
    g := ![![![-16, -10, 39], ![4, -151, 0]], ![![-2, 1, 0], ![6, 1, 0]]]
    h := ![![![-6013736, -18027497, 18029643], ![-113183, -318523520, 0]], ![![-660525, -1980074, 1980309], ![-12394, -34985440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {11} * I53N1 =  Ideal.span {B.equivFun.symm ![21878, 36, 519]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E53RS1 


noncomputable def E67RS0 : RelationCertificate Table 11 ![![67, 0, 0], ![-28, 1, 0]]
  ![-1136, -2, -27] ![![11, 0, 0], ![0, 1, 0]] where
    su := ![![737, 0, 0], ![-308, 11, 0]]
    hsu := by decide
    w := ![![-12496, -22, -297], ![-1375, 0, -33]]
    hw := by decide
    g := ![![![56, 57, -171], ![11, 625, 0]], ![![-23, -23, 69], ![-1, -252, 0]]]
    h := ![![![674042, 19443585, -2011419], ![8581, 44921682, 0]], ![![74184, 2139547, -221334], ![976, 4943125, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {11} * I67N0 =  Ideal.span {B.equivFun.symm ![-1136, -2, -27]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 3 ![![67, 0, 0], ![-22, 1, 0]]
  ![78, -102, 37] ![![3, 0, 0], ![29, 0, 1]] where
    su := ![![201, 0, 0], ![-66, 3, 0]]
    hsu := by decide
    w := ![![234, -306, 111], ![-1164, 1437, -468]]
    hw := by decide
    g := ![![![3997, 894, -3790], ![37395, 67, 0]], ![![-1257, -287, 1175], ![-11599, -23, 0]]]
    h := ![![![982, 22028, -2873], ![70, 64176, 0]], ![![-4705, -107719, 14049], ![-47, -313813, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {3} * I67N1 =  Ideal.span {B.equivFun.symm ![78, -102, 37]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 1089 ![![67, 0, 0], ![-17, 1, 0]]
  ![-303, 84, 166] ![![1089, 0, 0], ![62, 0, 1]] where
    su := ![![72963, 0, 0], ![-18513, 1089, 0]]
    hsu := by decide
    w := ![![-329967, 91476, 180774], ![-6534, 2178, 3267]]
    hw := by decide
    g := ![![![3460485533294957, 1361453243580800, 67891690601039], ![197078048444239, -74131129112974556, 0]], ![![-878034236727614, -345443593988831, -17226261506798], ![-50004911789097, 18809403692691847, 0]]]
    h := ![![![873, 15453, -2573], ![75, 57519, 0]], ![![22, 306, -51], ![20, 1140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {1089} * I67N2 =  Ideal.span {B.equivFun.symm ![-303, 84, 166]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E67RS2 


noncomputable def E71RS0 : RelationCertificate Table 99 ![![71, 0, 0], ![10, 1, 0]]
  ![30, -24, -5] ![![99, 0, 0], ![62, 0, 1]] where
    su := ![![7029, 0, 0], ![990, 99, 0]]
    hsu := by decide
    w := ![![2970, -2376, -495], ![396, -495, -99]]
    hw := by decide
    g := ![![![-6190221397588, -3379952032279, -129825726054], ![-3878015680467, 16730762559781, 0]], ![![-784678312462, -428445912740, -16456831685], ![-491580931253, 2120807268063, 0]]]
    h := ![![![950, -8626, -2875], ![62, 68040, 0]], ![![119, -1159, -386], ![69, 9135, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {99} * I71N0 =  Ideal.span {B.equivFun.symm ![30, -24, -5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 99 ![![71, 0, 0], ![-20, 1, 0]]
  ![-6, -15, 1] ![![99, 0, 0], ![62, 0, 1]] where
    su := ![![7029, 0, 0], ![-1980, 99, 0]]
    hsu := by decide
    w := ![![-594, -1485, 99], ![-1089, -297, 0]]
    hw := by decide
    g := ![![![-8208, -4463, -172], ![-5071, 22092, 0]], ![![1805, 1001, 38], ![1195, -4955, 0]]]
    h := ![![![30, 258, -37], ![63, 876, 0]], ![![43, 503, -72], ![68, 1704, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {99} * I71N1 =  Ideal.span {B.equivFun.symm ![-6, -15, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E71RS1 


noncomputable def E73RS0 : RelationCertificate Table 11 ![![73, 0, 0], ![-32, 1, 0]]
  ![-337, -1, -8] ![![11, 0, 0], ![0, 1, 0]] where
    su := ![![803, 0, 0], ![-352, 11, 0]]
    hsu := by decide
    w := ![![-3707, -11, -88], ![-407, 0, -11]]
    hw := by decide
    g := ![![![470290, 466438, -1410875], ![42404, 5173208, 0]], ![![-205451, -203769, 616355], ![-18515, -2259968, 0]]]
    h := ![![![211575, 6946421, -631496], ![2466, 15366400, 0]], ![![23235, 762703, -69337], ![281, 1687200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N0 : Ideal.span {11} * I73N0 =  Ideal.span {B.equivFun.symm ![-337, -1, -8]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E73RS0 


noncomputable def E73RS1 : RelationCertificate Table 1089 ![![73, 0, 0], ![-21, 1, 0]]
  ![1428, -1776, 587] ![![1089, 0, 0], ![62, 0, 1]] where
    su := ![![79497, 0, 0], ![-22869, 1089, 0]]
    hsu := by decide
    w := ![![1555092, -1934064, 639243], ![26136, -33759, 11979]]
    hw := by decide
    g := ![![![239277443263, 94138538989, 4694413538], ![13627085842, -5125843448018, 0]], ![![-68833240314, -27080950813, -1350447793], ![-3920119978, 1474557771786, 0]]]
    h := ![![![-6579, -144717, 19739], ![-75, -480120, 0]], ![![-110, -2434, 332], ![1, -8075, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {1089} * I73N1 =  Ideal.span {B.equivFun.symm ![1428, -1776, 587]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E73RS1 


noncomputable def E73RS2 : RelationCertificate Table 3 ![![73, 0, 0], ![-20, 1, 0]]
  ![12, -15, 5] ![![3, 0, 0], ![29, 0, 1]] where
    su := ![![219, 0, 0], ![-60, 3, 0]]
    hsu := by decide
    w := ![![36, -45, 15], ![-177, 210, -63]]
    hw := by decide
    g := ![![![-204, 2519, 217], ![-1740, 584, 0]], ![![33, -725, -61], ![481, -168, 0]]]
    h := ![![![-2105, -44324, 6332], ![20, -154077, 0]], ![![10405, 217704, -31101], ![142, 756784, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N2 : Ideal.span {3} * I73N2 =  Ideal.span {B.equivFun.symm ![12, -15, 5]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E73RS2 


noncomputable def E79RS1 : RelationCertificate Table 9 ![![79, 0, 0], ![-26, 1, 0]]
  ![-57, 33, 14] ![![9, 0, 0], ![26, 0, 1]] where
    su := ![![711, 0, 0], ![-234, 9, 0]]
    hsu := by decide
    w := ![![-513, 297, 126], ![873, -486, -234]]
    hw := by decide
    g := ![![![-945, 570, 100], ![-2696, 327, 0]], ![![71368, -207632, -9765], ![205141, -116795, 0]]]
    h := ![![![-1777, -47968, 5330], ![1, -140352, 0]], ![![3041, 81121, -9014], ![107, 237360, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {9} * I79N1 =  Ideal.span {B.equivFun.symm ![-57, 33, 14]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E79RS1 
