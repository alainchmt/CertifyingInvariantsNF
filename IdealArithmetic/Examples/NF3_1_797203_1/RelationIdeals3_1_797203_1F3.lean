import IdealArithmetic.Examples.NF3_1_797203_1.PrimesBelow3_1_797203_1F3
import IdealArithmetic.Examples.NF3_1_797203_1.ClassGroupData3_1_797203_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 6 ![![139, 0, 0], ![17, 1, 0]]
  ![1719199, 1820081, -1537305] ![![6, 0, 0], ![36, 1, 2]] where
    su := ![![834, 0, 0], ![102, 6, 0]]
    hsu := by decide
    w := ![![10315194, 10920486, -9223830], ![74629980, -66117498, 36446706]]
    hw := by decide
    g := ![![![9914006776723, -789707784420, -7463882762124], ![56864461775609, 0, 0]], ![![1570848888188, -125127168369, -1182633036531], ![9010027788972, 0, 0]]]
    h := ![![![107633817, 879917907, 220000205], ![19494208, -7645391450, 0]], ![![795750321, 6505181906, 1626618209], ![144121883, -56523464150, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {6} * I139N1 =  Ideal.span {B.equivFun.symm ![1719199, 1820081, -1537305]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E139RS1 


noncomputable def E149RS0 : RelationCertificate Table 2 ![![149, 0, 0], ![16, 1, 0]]
  ![31, 1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![298, 0, 0], ![32, 2, 0]]
    hsu := by decide
    w := ![![62, 2, 2], ![154, 4, 6]]
    hw := by decide
    g := ![![![19, -4, 1], ![-1, 0, 0]], ![![3, -1, 0], ![1, 0, 0]]]
    h := ![![![-461, -3491, -931], ![-40, 34680, 0]], ![![-1143, -8673, -2313], ![-121, 86160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N0 : Ideal.span {2} * I149N0 =  Ideal.span {B.equivFun.symm ![31, 1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E149RS0 


noncomputable def E149RS2 : RelationCertificate Table 2 ![![149, 0, 0], ![-43, 1, 0]]
  ![-24801474902772, -613692277696, -811710552963] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![298, 0, 0], ![-86, 2, 0]]
    hsu := by decide
    w := ![![-49602949805544, -1227384555392, -1623421105926], ![-124607388605768, -3083308248038, -4078190216710]]
    hw := by decide
    g := ![![![19060854, -3224334, 168217], ![-1612165, 0, 0]], ![![-5383279, 1031009, -154487], ![515506, 0, 0]]]
    h := ![![![-6448361273138170, 160494414725620850, -14592199766213335], ![2938080197789126, 543559238363808488, 0]], ![![-16198904746235667, 403177431648137906, -36657011609384479], ![7380740508297163, 1365473172675794754, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N2 : Ideal.span {2} * I149N2 =  Ideal.span {B.equivFun.symm ![-24801474902772, -613692277696, -811710552963]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E149RS2 


noncomputable def E151RS0 : RelationCertificate Table 2 ![![151, 0, 0], ![0, 1, 0]]
  ![1, -3, 2] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![302, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![2, -6, 4], ![298, -48, -8]]
    hw := by decide
    g := ![![![1832, 36, 60], ![19, 0, 0]], ![![61, 1, 2], ![1, 0, 0]]]
    h := ![![![-3, 1, -6], ![73, 227, 0]], ![![-447, 223, -896], ![126, 33823, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N0 : Ideal.span {2} * I151N0 =  Ideal.span {B.equivFun.symm ![1, -3, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E151RS0 


noncomputable def E157RS1 : RelationCertificate Table 6 ![![157, 0, 0], ![-36, 1, 0]]
  ![-71368681, 14250589, -32409] ![![6, 0, 0], ![36, 1, 2]] where
    su := ![![942, 0, 0], ![-216, 6, 0]]
    hsu := by decide
    w := ![![-428212086, 85503534, -194454], ![1779934932, -314406510, -28343742]]
    hw := by decide
    g := ![![![116278893219987, -9262284080245, -87542004584928], ![666948977111663, 0, 0]], ![![-22941608866367, 1827431382375, 17271874309679], ![-131587789864537, 0, 0]]]
    h := ![![![-734608341, 14691780415, -1588471405], ![262023562, 62347494544, 0]], ![![3052878454, -61055908593, 6601322407], ![-1088914152, -259103085464, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {6} * I157N1 =  Ideal.span {B.equivFun.symm ![-71368681, 14250589, -32409]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 2 ![![163, 0, 0], ![41, 1, 0]]
  ![6386, 158, 209] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![326, 0, 0], ![82, 2, 0]]
    hsu := by decide
    w := ![![12772, 316, 418], ![32084, 794, 1050]]
    hw := by decide
    g := ![![![-56, 34, -23], ![19, 0, 0]], ![![-35, 11, -5], ![6, 0, 0]]]
    h := ![![![76672, 1681836, 168203], ![29690, -6854220, 0]], ![![192618, 4224863, 422535], ![74528, -17218170, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {2} * I163N1 =  Ideal.span {B.equivFun.symm ![6386, 158, 209]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 3 ![![167, 0, 0], ![-57, 1, 0]]
  ![-4386905731, -108550406, -143576045] ![![3, 0, 0], ![18, -1, 1]] where
    su := ![![501, 0, 0], ![-171, 3, 0]]
    hsu := by decide
    w := ![![-13160717193, -325651218, -430728135], ![-87924485763, -2175619722, -2877620514]]
    hw := by decide
    g := ![![![5476, -27687, -15915], ![36836, 0, 0]], ![![-1828, 11399, 4644], ![-13211, 0, 0]]]
    h := ![![![123318737878, -4244818450141, 292773074405], ![-67508901219, -12223311750420, 0]], ![![823871256632, -28358901259913, 1955966505078], ![-451015346631, -81661841388716, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {3} * I167N1 =  Ideal.span {B.equivFun.symm ![-4386905731, -108550406, -143576045]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E167RS1 


noncomputable def E179RS1 : RelationCertificate Table 6 ![![179, 0, 0], ![30, 1, 0]]
  ![4889, 121, 160] ![![6, 0, 0], ![36, 1, 2]] where
    su := ![![1074, 0, 0], ![180, 6, 0]]
    hsu := by decide
    w := ![![29334, 726, 960], ![269670, 6672, 8826]]
    hw := by decide
    g := ![![![-2, -40, -9], ![29, 0, 0]], ![![-13, -6, -3], ![7, 0, 0]]]
    h := ![![![329773, 4983208, 687404], ![83270, -30761289, 0]], ![![3031867, 45811132, 6319373], ![764130, -282791574, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {6} * I179N1 =  Ideal.span {B.equivFun.symm ![4889, 121, 160]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E179RS1 


noncomputable def E191RS1 : RelationCertificate Table 2 ![![191, 0, 0], ![87, 1, 0]]
  ![-24001, 18803, -9972] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![382, 0, 0], ![174, 2, 0]]
    hsu := by decide
    w := ![![-48002, 37606, -19944], ![-1478138, 216468, 55268]]
    hw := by decide
    g := ![![![-48854070622, -967083321, -1598911550], ![-483541659, 0, 0]], ![![-23537991665, -465942732, -770358872], ![-232971366, 0, 0]]]
    h := ![![![532205, 30796481, 1432436], ![403764, -68401312, 0]], ![![16286952, 942386787, 43835070], ![12352741, -2093117684, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {2} * I191N1 =  Ideal.span {B.equivFun.symm ![-24001, 18803, -9972]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 3 ![![193, 0, 0], ![-71, 1, 0]]
  ![56862, 1407, 1861] ![![3, 0, 0], ![18, -1, 1]] where
    su := ![![579, 0, 0], ![-213, 3, 0]]
    hsu := by decide
    w := ![![170586, 4221, 5583], ![1139655, 28200, 37299]]
    hw := by decide
    g := ![![![-25, 108, 61], ![-142, 0, 0]], ![![5, -46, -20], ![55, 0, 0]]]
    h := ![![![26075230, -1144166027, 63569257], ![-15520702, -3067216185, 0]], ![![174203924, -7643971549, 424695001], ![-103691323, -20491530690, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {3} * I193N1 =  Ideal.span {B.equivFun.symm ![56862, 1407, 1861]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E193RS1 
