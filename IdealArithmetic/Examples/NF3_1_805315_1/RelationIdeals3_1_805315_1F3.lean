import IdealArithmetic.Examples.NF3_1_805315_1.PrimesBelow3_1_805315_1F3
import IdealArithmetic.Examples.NF3_1_805315_1.ClassGroupData3_1_805315_1

set_option linter.all false

noncomputable section


noncomputable def E151RS1 : RelationCertificate Table 4 ![![151, 0, 0], ![-73, 1, 0]]
  ![342148572167, -8182834032, -10740756993] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![604, 0, 0], ![-292, 4, 0]]
    hsu := by decide
    w := ![![1368594288668, -32731336128, -42963027972], ![2362966538460, 43965299324, -40914170160]]
    hw := by decide
    g := ![![![-786814810763274226489, 133897934947618488568, -50438403758742315222], ![33474483736904622146, -50715, 0]], ![![453867086176439349862, -77237826167461677124, 29094942078128557866], ![-19309456541865419277, 24150, 0]]]
    h := ![![![51467488579461, -730209880660, 1675580207], ![106455460642828, -52750673650, 0]], ![![88828441946643, -1260159328345, 2950159810], ![183732931401486, -91140534770, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {4} * I151N1 =  Ideal.span {B.equivFun.symm ![342148572167, -8182834032, -10740756993]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 4 ![![157, 0, 0], ![25, 1, 0]]
  ![-508548638551, 21427471260, 19031676477] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![628, 0, 0], ![100, 4, 0]]
    hsu := by decide
    w := ![![-2034194554204, 85709885040, 76126705908], ![-4186968824940, 26734097588, 107137356300]]
    hw := by decide
    g := ![![![-1742161950517913437204, 296476228367347367184, -111680495424454244059], ![74119057091836841797, 221, 0]], ![![-120919361589604473235, 20577717387304866236, -7751480397514797540], ![5144429346826216560, 39, 0]]]
    h := ![![![997821582757, 36374031144, -610486709], ![-6286661485256, 22975617958, 0]], ![![2046184632345, 74331844571, -1334167740], ![-12891909179376, 47249734851, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {4} * I157N1 =  Ideal.span {B.equivFun.symm ![-508548638551, 21427471260, 19031676477]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 2 ![![163, 0, 0], ![13, 1, 0]]
  ![-3691, 430, 229] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![326, 0, 0], ![26, 2, 0]]
    hsu := by decide
    w := ![![-7382, 860, 458], ![-50380, 2922, 2150]]
    hw := by decide
    g := ![![![-995881, 108380, -286808], ![54190, 89187, 0]], ![![6739, -4100, -19098], ![-2049, 7812, 0]]]
    h := ![![![-87150, -6751, -17], ![1092443, 600, 0]], ![![-594716, -46067, -115], ![7454886, 3964, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {2} * I163N1 =  Ideal.span {B.equivFun.symm ![-3691, 430, 229]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E163RS1 


noncomputable def E173RS0 : RelationCertificate Table 2 ![![173, 0, 0], ![32, 1, 0]]
  ![-23761, 928, 865] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![346, 0, 0], ![64, 2, 0]]
    hsu := by decide
    w := ![![-47522, 1856, 1730], ![-190300, 522, 4640]]
    hw := by decide
    g := ![![![15031657, -2192858, 847855], ![-1096427, 46297, 0]], ![![1555038, -228807, 75500], ![-114403, 9674, 0]]]
    h := ![![![-1373461, -44462, -230], ![7424531, 8131, 0]], ![![-5499878, -178013, -920], ![29730742, 32296, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N0 : Ideal.span {2} * I173N0 =  Ideal.span {B.equivFun.symm ![-23761, 928, 865]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E173RS0 


noncomputable def E173RS1 : RelationCertificate Table 2 ![![173, 0, 0], ![70, 1, 0]]
  ![4142111, -663400, -316859] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![346, 0, 0], ![140, 2, 0]]
    hsu := by decide
    w := ![![8284222, -1326800, -633718], ![69708980, -5076482, -3317000]]
    hw := by decide
    g := ![![![2308607017381, -333941403966, 147992299413], ![-166970701981, -40769, 0]], ![![745920276120, -107897818567, 47816919770], ![-53948909283, -16584, 0]]]
    h := ![![![474568447, 7824377, 72042], ![-1172802846, -2556025, 0]], ![![3993532750, 65857674, 611875], ![-9869233018, -21502575, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {2} * I173N1 =  Ideal.span {B.equivFun.symm ![4142111, -663400, -316859]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E173RS1 


noncomputable def E179RS1 : RelationCertificate Table 4 ![![179, 0, 0], ![-75, 1, 0]]
  ![-3036135, 53336, 88929] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![716, 0, 0], ![-300, 4, 0]]
    hsu := by decide
    w := ![![-12144540, 213344, 355716], ![-19564380, -581716, 266680]]
    hw := by decide
    g := ![![![64304204997, -10943109110, 4122191224], ![-2735777274, 353, 0]], ![![-32009483470, 5447284041, -2051953125], ![1361821011, -144, 0]]]
    h := ![![![-133517865, 1963398, -11874], ![-318622156, 442875, 0]], ![![-215063505, 3161411, -19565], ![-513219684, 713761, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {4} * I179N1 =  Ideal.span {B.equivFun.symm ![-3036135, 53336, 88929]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E179RS1 


noncomputable def E191RS1 : RelationCertificate Table 2 ![![191, 0, 0], ![-73, 1, 0]]
  ![-13, 2, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![382, 0, 0], ![-146, 2, 0]]
    hsu := by decide
    w := ![![-26, 4, 2], ![-220, 16, 10]]
    hw := by decide
    g := ![![![31, -4, 1], ![-1, 0, 0]], ![![-13, 2, 7], ![3, -3, 0]]]
    h := ![![![-1775, 82, -4], ![-4644, 153, 0]], ![![-16176, 294, -5], ![-42322, 192, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {2} * I191N1 =  Ideal.span {B.equivFun.symm ![-13, 2, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 4 ![![193, 0, 0], ![-1, 1, 0]]
  ![-115667821, 16931916, 8320719] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![772, 0, 0], ![-4, 4, 0]]
    hsu := by decide
    w := ![![-462671284, 67727664, 33282876], ![-1830558180, 125923508, 84659580]]
    hw := by decide
    g := ![![![-376021295051566, 63990248041156, -24104673228183], ![15997562010293, 2895, 0]], ![![29425126447957, -5007485386720, 1886284279536], ![-1251871346676, -15, 0]]]
    h := ![![![-1198592, 687007, 43083], ![-115660435, 1140, 0]], ![![-4742242, 2534166, 109585], ![-457613161, 2998, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {4} * I193N1 =  Ideal.span {B.equivFun.symm ![-115667821, 16931916, 8320719]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E193RS1 
