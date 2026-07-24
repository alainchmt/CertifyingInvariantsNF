import IdealArithmetic.Examples.NF3_1_780332_1.PrimesBelow3_1_780332_1F3
import IdealArithmetic.Examples.NF3_1_780332_1.ClassGroupData3_1_780332_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 81 ![![139, 0, 0], ![-23, 1, 0]]
  ![405, 20, -4] ![![81, 0, 0], ![-63, -4, 1]] where
    su := ![![11259, 0, 0], ![-1863, 81, 0]]
    hsu := by decide
    w := ![![32805, 1620, -324], ![-5427, -648, 81]]
    hw := by decide
    g := ![![![345937988, 47491718, -642299], ![-271415953, -80860542, 0]], ![![-54188235, -7439176, 100610], ![42515090, 12666125, 0]]]
    h := ![![![764534, -34092, 37], ![4620427, -5147, 0]], ![![-126452, 5659, -7], ![-764207, 974, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {81} * I139N1 =  Ideal.span {B.equivFun.symm ![405, 20, -4]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E139RS1 


noncomputable def E157RS0 : RelationCertificate Table 9 ![![157, 0, 0], ![22, 1, 0]]
  ![-2211, -191, 28] ![![9, 0, 0], ![-84, -10, 1]] where
    su := ![![1413, 0, 0], ![198, 9, 0]]
    hsu := by decide
    w := ![![-19899, -1719, 252], ![-77094, -4626, 819]]
    hw := by decide
    g := ![![![737991, -2014997, -275882], ![-4678891, -716222, 0]], ![![113548, -309975, -42439], ![-719842, -110188, 0]]]
    h := ![![![-14179, -671, -1], ![101086, 185, 0]], ![![-54834, -2550, -2], ![390926, 405, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N0 : Ideal.span {9} * I157N0 =  Ideal.span {B.equivFun.symm ![-2211, -191, 28]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E157RS0 


noncomputable def E157RS1 : RelationCertificate Table 81 ![![157, 0, 0], ![35, 1, 0]]
  ![-1017, -167, 19] ![![81, 0, 0], ![-63, -4, 1]] where
    su := ![![12717, 0, 0], ![2835, 81, 0]]
    hsu := by decide
    w := ![![-82377, -13527, 1539], ![-71523, -4941, 810]]
    hw := by decide
    g := ![![![37213259, 5108753, -69098], ![-29196742, -8698352, 0]], ![![10282609, 1411628, -19093], ![-8067518, -2403492, 0]]]
    h := ![![![-2026, -63, 0], ![9059, 19, 0]], ![![-1734, -87, -1], ![7753, 167, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {81} * I157N1 =  Ideal.span {B.equivFun.symm ![-1017, -167, 19]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E157RS1 


noncomputable def E157RS2 : RelationCertificate Table 729 ![![157, 0, 0], ![-57, 1, 0]]
  ![4095, 1222, 94] ![![729, 0, 0], ![-1980, -221, 26]] where
    su := ![![114453, 0, 0], ![-41553, 729, 0]]
    hsu := by decide
    w := ![![2985255, 890838, 68526], ![-1971216, -597051, -46656]]
    hw := by decide
    g := ![![![-25874623613, 2664592416, 790852480], ![69497178470, 10784878270, 0]], ![![9267417093, -954366715, -283256642], ![-24891538920, -3862778750, 0]]]
    h := ![![![177583407, -3463099, 6099], ![489133172, -957449, 0]], ![![-117259246, 2286747, -4028], ![-322977174, 632332, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N2 : Ideal.span {729} * I157N2 =  Ideal.span {B.equivFun.symm ![4095, 1222, 94]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E157RS2 


noncomputable def E163RS1 : RelationCertificate Table 729 ![![163, 0, 0], ![42, 1, 0]]
  ![-2745, -163, 29] ![![729, 0, 0], ![-1980, -221, 26]] where
    su := ![![118827, 0, 0], ![30618, 729, 0]]
    hsu := by decide
    w := ![![-2001105, -118827, 21141], ![-505926, 29889, 729]]
    hw := by decide
    g := ![![![-9128959729, 940108648, 279024754], ![24519659165, 3805068706, 0]], ![![-2524703314, 259996383, 77167041], ![6781153836, 1052329288, 0]]]
    h := ![![![-37587, -987, -2], ![145808, 355, 0]], ![![-9538, -269, -1], ![37000, 164, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {729} * I163N1 =  Ideal.span {B.equivFun.symm ![-2745, -163, 29]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 27 ![![167, 0, 0], ![28, 1, 0]]
  ![1701, 127, -20] ![![27, 0, 0], ![654, 35, -8]] where
    su := ![![4509, 0, 0], ![756, 27, 0]]
    hsu := by decide
    w := ![![45927, 3429, -540], ![154926, 19089, -2403]]
    hw := by decide
    g := ![![![-371, 9499, 1889], ![17758, 2600, 0]], ![![-356, 1590, 323], ![3017, 440, 0]]]
    h := ![![![1659, 35, -1], ![-9834, 147, 0]], ![![5686, 193, -1], ![-33708, 78, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {27} * I167N1 =  Ideal.span {B.equivFun.symm ![1701, 127, -20]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 531441 ![![173, 0, 0], ![-8, 1, 0]]
  ![-91755, -27635, -2159] ![![531441, 0, 0], ![163602, 167, 1]] where
    su := ![![91939293, 0, 0], ![-4251528, 531441, 0]]
    hsu := by decide
    w := ![![-48762368955, -14686372035, -1147381119], ![-15227910414, -4585804389, -358191234]]
    hw := by decide
    g := ![![![-144205, -8611231, -8784], ![373096, 27950960, 0]], ![![-42520, 397279, 405], ![142520, -1289680, 0]]]
    h := ![![![-292159, 36370, -22], ![-6306469, 1647, 0]], ![![-91238, 11359, -7], ![-1969440, 537, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {531441} * I173N1 =  Ideal.span {B.equivFun.symm ![-91755, -27635, -2159]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E173RS1 


noncomputable def E181RS1 : RelationCertificate Table 6561 ![![181, 0, 0], ![-6, 1, 0]]
  ![-261, 32, 17] ![![6561, 0, 0], ![34461, 104, -422]] where
    su := ![![1187541, 0, 0], ![-39366, 6561, 0]]
    hsu := by decide
    w := ![![-1712421, 209952, 111537], ![-15543009, -4382748, -190269]]
    hw := by decide
    g := ![![![1090838, 2317996, 361657], ![5840977, 885198, 0]], ![![-44439, -36021, -5270], ![-85317, -13724, 0]]]
    h := ![![![-10387491, 1733133, -314], ![-313355935, 56851, 0]], ![![-94269683, 15728671, -2844], ![-2843801709, 514735, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {6561} * I181N1 =  Ideal.span {B.equivFun.symm ![-261, 32, 17]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 531441 ![![191, 0, 0], ![75, 1, 0]]
  ![23013, 1613, -229] ![![531441, 0, 0], ![163602, 167, 1]] where
    su := ![![101505231, 0, 0], ![39858075, 531441, 0]]
    hsu := by decide
    w := ![![12230051733, 857214333, -121699989], ![3744533286, 263063295, -37200870]]
    hw := by decide
    g := ![![![-46224113578117, -15281992787750242, -15587554395221], ![-19032151682513, 49604098967079800, 0]], ![![-18553773894471, -6133998358171178, -6256646917465], ![-7639264208028, 19910457088195960, 0]]]
    h := ![![![384866909268, 6765349362, 21783873], ![-980127728629, -4160719972, 0]], ![![117836699506, 2071381423, 6669672], ![-300090794648, -1273907422, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {531441} * I191N1 =  Ideal.span {B.equivFun.symm ![23013, 1613, -229]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 243 ![![193, 0, 0], ![-42, 1, 0]]
  ![-3357, -1001, -77] ![![243, 0, 0], ![-144, -4, 1]] where
    su := ![![46899, 0, 0], ![-10206, 243, 0]]
    hsu := by decide
    w := ![![-815751, -243243, -18711], ![96714, 28674, 2187]]
    hw := by decide
    g := ![![![3431715201, -199549197, -24869647], ![-2030426359, -2018437568, 0]], ![![-701843730, 40811195, 5086263], ![415256856, 412804672, 0]]]
    h := ![![![-22947, 566, -1], ![-105367, 116, 0]], ![![2798, -64, 0], ![12848, 9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {243} * I193N1 =  Ideal.span {B.equivFun.symm ![-3357, -1001, -77]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E193RS1 
