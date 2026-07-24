import IdealArithmetic.Examples.NF3_1_603288_2.PrimesBelow3_1_603288_2F3
import IdealArithmetic.Examples.NF3_1_603288_2.ClassGroupData3_1_603288_2

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 400 ![![139, 0, 0], ![43, 1, 0]]
  ![-76, 5, -6] ![![400, 0, 0], ![-115, 6, 1]] where
    su := ![![55600, 0, 0], ![17200, 400, 0]]
    hsu := by decide
    w := ![![-30400, 2000, -2400], ![4400, -800, 800]]
    hw := by decide
    g := ![![![-30785349499, 32389562296, -2896943341], ![9329389225, 95678946972, -9563114]], ![![-10023136988, 10545438916, -943190859], ![3037475885, 31151285160, -3113572]]]
    h := ![![![-791242, -21066, -124], ![2557734, 8615, 0]], ![![114351, 3003, 16], ![-369646, -1111, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {400} * I139N1 =  Ideal.span {B.equivFun.symm ![-76, 5, -6]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 40 ![![149, 0, 0], ![-15, 1, 0]]
  ![-36, -5, -1] ![![40, 0, 0], ![5, 6, 1]] where
    su := ![![5960, 0, 0], ![-600, 40, 0]]
    hsu := by decide
    w := ![![-1440, -200, -40], ![-1720, -80, -80]]
    hw := by decide
    g := ![![![-2741, 358, -231], ![-271, 792, 0]], ![![253, -37, 21], ![49, -74, 0]]]
    h := ![![![-24, 9, -1], ![-236, 74, 0]], ![![-47, 18, -2], ![-464, 148, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {40} * I149N1 =  Ideal.span {B.equivFun.symm ![-36, -5, -1]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E149RS1 


noncomputable def E151RS1 : RelationCertificate Table 6400 ![![151, 0, 0], ![-64, 1, 0]]
  ![348, -65, -12] ![![6400, 0, 0], ![14565, -1746, 1129]] where
    su := ![![966400, 0, 0], ![-409600, 6400, 0]]
    hsu := by decide
    w := ![![2227200, -416000, -76800], ![-2272000, -1401600, 729600]]
    hw := by decide
    g := ![![![8075122367620467, 1950630470931080, -4061202494793118], ![17128634197748031, -1905347368855512, 552780514]], ![![-3388163231171843, -818446351439226, 1704001046765998], ![-7186839523528884, 799446448470780, -231935880]]]
    h := ![![![12548, -199, 0], ![29600, -6, 0]], ![![-12629, 220, 0], ![-29791, 57, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {6400} * I151N1 =  Ideal.span {B.equivFun.symm ![348, -65, -12]} * (J0 ^ 11*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_2 E151RS1 


noncomputable def E157RS1 : RelationCertificate Table 8 ![![157, 0, 0], ![12, 1, 0]]
  ![12, 1, 0] ![![8, 0, 0], ![13, 2, 1]] where
    su := ![![1256, 0, 0], ![96, 8, 0]]
    hsu := by decide
    w := ![![96, 8, 0], ![296, 16, 16]]
    hw := by decide
    g := ![![![7150329, -272310, -2138677], ![11283897, 0, -728190]], ![![591751, -22536, -176994], ![933840, 0, -60264]]]
    h := ![![![972, 81, 0], ![-12716, 0, 0]], ![![3013, 251, 0], ![-39417, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {8} * I157N1 =  Ideal.span {B.equivFun.symm ![12, 1, 0]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E157RS1 


noncomputable def E163RS1 : RelationCertificate Table 3200 ![![163, 0, 0], ![-80, 1, 0]]
  ![-12, 35, 3] ![![3200, 0, 0], ![285, 126, 1]] where
    su := ![![521600, 0, 0], ![-256000, 3200, 0]]
    hsu := by decide
    w := ![![-38400, 112000, 9600], ![54400, 0, 9600]]
    hw := by decide
    g := ![![![-177, -33, 56], ![2347, -720, 0]], ![![-1141865, -2177163, -2085139], ![-186140, 26478694, 0]]]
    h := ![![![-3934884, 56667, -187], ![-8017326, 15242, 0]], ![![5513099, -79433, 263], ![11232939, -21433, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {3200} * I163N1 =  Ideal.span {B.equivFun.symm ![-12, 35, 3]} * (J0 ^ 10*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_10J1_2 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 3200 ![![167, 0, 0], ![-56, 1, 0]]
  ![-36, 55, -16] ![![3200, 0, 0], ![-355, 62, 1]] where
    su := ![![534400, 0, 0], ![-179200, 3200, 0]]
    hsu := by decide
    w := ![![-115200, 176000, -51200], ![-118400, -3200, 12800]]
    hw := by decide
    g := ![![![299561306309909464, -818186221432995822, 270155778534381657], ![-49000516778224743, -6971366862259947576, -337740484]], ![![-98589797020930572, 269276477960575314, -88912028385206659], ![16126752358627484, 2294373904210459656, 111155096]]]
    h := ![![![36, 53, -2], ![108, 159, 0]], ![![37, 0, 0], ![111, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {3200} * I167N1 =  Ideal.span {B.equivFun.symm ![-36, 55, -16]} * (J0 ^ 9*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9J1_2 E167RS1 


noncomputable def E179RS0 : RelationCertificate Table 160 ![![179, 0, 0], ![17, 1, 0]]
  ![-64, 10, 1] ![![160, 0, 0], ![-35, 30, 1]] where
    su := ![![28640, 0, 0], ![2720, 160, 0]]
    hsu := by decide
    w := ![![-10240, 1600, 160], ![7840, -3040, 480]]
    hw := by decide
    g := ![![![43752782, -16251813, 20000503], ![-12493057, -53126458, 0]], ![![4599375, -1708434, 2102478], ![-1313167, -5584722, 0]]]
    h := ![![![-145036, -8625, -11], ![1527140, 985, 0]], ![![110972, 6587, 7], ![-1168467, -625, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N0 : Ideal.span {160} * I179N0 =  Ideal.span {B.equivFun.symm ![-64, 10, 1]} * (J0 ^ 8*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_1 E179RS0 


noncomputable def E179RS1 : RelationCertificate Table 20 ![![179, 0, 0], ![69, 1, 0]]
  ![36, 0, 1] ![![20, 0, 0], ![5, 2, 1]] where
    su := ![![3580, 0, 0], ![1380, 20, 0]]
    hsu := by decide
    w := ![![720, 0, 20], ![460, 100, 20]]
    hw := by decide
    g := ![![![-2, -1, -1], ![17, 0, 0]], ![![-652, 92, -13], ![-133, 98, 0]]]
    h := ![![![30960, 483, 1], ![-80316, -89, 0]], ![![19780, 321, 1], ![-51313, -89, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {20} * I179N1 =  Ideal.span {B.equivFun.symm ![36, 0, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E179RS1 


noncomputable def E179RS2 : RelationCertificate Table 80 ![![179, 0, 0], ![-86, 1, 0]]
  ![372, 25, 12] ![![80, 0, 0], ![45, 6, 1]] where
    su := ![![14320, 0, 0], ![-6880, 80, 0]]
    hsu := by decide
    w := ![![29760, 2000, 960], ![30320, 2160, 960]]
    hw := by decide
    g := ![![![31555794805378091, 5800145351746525, 3355749990575692], ![18227092354288413, -23890590948710024, -8992646]], ![![-15074424270456165, -2770770072558585, -1603065282161606], ![-8707209723600454, 11412702682785712, 4295850]]]
    h := ![![![3399756, -45033, 128], ![7076232, -11450, 0]], ![![3463655, -45862, 130], ![7209231, -11629, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N2 : Ideal.span {80} * I179N2 =  Ideal.span {B.equivFun.symm ![372, 25, 12]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E179RS2 


noncomputable def E193RS1 : RelationCertificate Table 64 ![![193, 0, 0], ![50, 1, 0]]
  ![-36, 7, 0] ![![64, 0, 0], ![29, 30, 1]] where
    su := ![![12352, 0, 0], ![3200, 64, 0]]
    hsu := by decide
    w := ![![-2304, 448, 0], ![-64, -1024, 384]]
    hw := by decide
    g := ![![![122102428, -36501184, -331516], ![38212639, 0, -2124458]], ![![34075099, -10186374, -92516], ![10663986, 0, -592872]]]
    h := ![![![-66952, -1489, -6], ![258434, 579, 0]], ![![-2007, -91, -2], ![7747, 196, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {64} * I193N1 =  Ideal.span {B.equivFun.symm ![-36, 7, 0]} * (J0 ^ 11*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_0 E193RS1 
