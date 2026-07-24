import IdealArithmetic.Examples.NF3_1_649415_1.PrimesBelow3_1_649415_1F3
import IdealArithmetic.Examples.NF3_1_649415_1.ClassGroupData3_1_649415_1

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 243 ![![139, 0, 0], ![20, 1, 0]]
  ![86926, 627, -3761] ![![243, 0, 0], ![-85, 1, 0]] where
    su := ![![33777, 0, 0], ![4860, 243, 0]]
    hsu := by decide
    w := ![![21123018, 152361, -913923], ![-7977933, 2916, 319059]]
    hw := by decide
    g := ![![![619582405, -31875765668, 1853321449], ![-347902138, -90071596098, 0]], ![![-650073907029944, 33441892997770700, -1944383436579624], ![365013066235999, 94497035017731293, 0]]]
    h := ![![![238174, 2326104, 612201], ![51031, -17019940, 0]], ![![-90065, -879495, -231473], ![-19211, 6435212, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {243} * I139N1 =  Ideal.span {B.equivFun.symm ![86926, 627, -3761]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E139RS1 


noncomputable def E157RS1 : RelationCertificate Table 3 ![![157, 0, 0], ![-59, 1, 0]]
  ![2818, -42, -95] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![471, 0, 0], ![-177, 3, 0]]
    hsu := by decide
    w := ![![8454, -126, -285], ![-17817, 2142, -210]]
    hw := by decide
    g := ![![![-324887, -73931, -23590], ![83654, 0, 0]], ![![99822, 22720, 7235], ![-25699, 8, 0]]]
    h := ![![![1940524, -71566760, 5964525], ![-1184962, -187286104, 0]], ![![-4092450, 150935199, -12579260], ![2499471, 394988750, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {3} * I157N1 =  Ideal.span {B.equivFun.symm ![2818, -42, -95]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E157RS1 


noncomputable def E163RS0 : RelationCertificate Table 729 ![![163, 0, 0], ![55, 1, 0]]
  ![362156, 47271, 24218] ![![729, 0, 0], ![-328, 1, 0]] where
    su := ![![118827, 0, 0], ![40095, 729, 0]]
    hsu := by decide
    w := ![![264011724, 34460559, 17654922], ![-114890400, -14996259, -7682931]]
    hw := by decide
    g := ![![![-45919587749327, 10109268562368980, -153637020149629], ![34527974409665, 22400277537815790, 0]], ![![-15447386880868, 3400766213720521, -51683619252778], ![11615238835235, 7535471687054999, 0]]]
    h := ![![![-37083869511, -1181159373256, -109377832859], ![-19759338539, 3565717356047, 0]], ![![16137846171, 514006994684, 47598124712], ![8598702763, -1551698867719, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N0 : Ideal.span {729} * I163N0 =  Ideal.span {B.equivFun.symm ![362156, 47271, 24218]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E163RS0 


noncomputable def E163RS1 : RelationCertificate Table 3 ![![163, 0, 0], ![-35, 1, 0]]
  ![-106, 33, -10] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![489, 0, 0], ![-105, 3, 0]]
    hsu := by decide
    w := ![![-318, 99, -30], ![-1398, -252, 165]]
    hw := by decide
    g := ![![![4476, 1018, 325], ![-1151, 0, 0]], ![![-661, -156, -35], ![169, -8, 0]]]
    h := ![![![-11050, 213205, -29615], ![3710, 965447, 0]], ![![-48412, 934210, -129765], ![16286, 4230350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {3} * I163N1 =  Ideal.span {B.equivFun.symm ![-106, 33, -10]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E163RS1 


noncomputable def E163RS2 : RelationCertificate Table 3 ![![163, 0, 0], ![-20, 1, 0]]
  ![172079, 22461, 11507] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![489, 0, 0], ![-60, 3, 0]]
    hsu := by decide
    w := ![![516237, 67383, 34521], ![1679442, 219213, 112305]]
    hw := by decide
    g := ![![![1682, 335, -154], ![-446, 0, 0]], ![![-334, -57, 37], ![94, -8, 0]]]
    h := ![![![-7509879, 80681266, -19211791], ![1416551, 626306688, 0]], ![![-24431454, 262475389, -62500535], ![4608152, 2037524928, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N2 : Ideal.span {3} * I163N2 =  Ideal.span {B.equivFun.symm ![172079, 22461, 11507]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E163RS2 


noncomputable def E173RS1 : RelationCertificate Table 729 ![![173, 0, 0], ![-33, 1, 0]]
  ![-425, -30, 4] ![![729, 0, 0], ![-328, 1, 0]] where
    su := ![![126117, 0, 0], ![-24057, 729, 0]]
    hsu := by decide
    w := ![![-309825, -21870, 2916], ![139968, 9477, -1458]]
    hw := by decide
    g := ![![![2427512051, -534420532797, 8121930648], ![-1825300889, -1184177488480, 0]], ![![-332086643, 73109392763, -1111090202], ![249703476, 161996951452, 0]]]
    h := ![![![-45930, 824775, -121302], ![13595, 4197050, 0]], ![![20773, -372612, 54801], ![-6021, -1896115, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {729} * I173N1 =  Ideal.span {B.equivFun.symm ![-425, -30, 4]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E173RS1 


noncomputable def E179RS1 : RelationCertificate Table 729 ![![179, 0, 0], ![-32, 1, 0]]
  ![15295, 222, -710] ![![729, 0, 0], ![-328, 1, 0]] where
    su := ![![130491, 0, 0], ![-23328, 729, 0]]
    hsu := by decide
    w := ![![11150055, 161838, -517590], ![-5127786, -63423, 233280]]
    hw := by decide
    g := ![![![1789003881, -393851919614, 5985619540], ![-1345191962, -872703327078, 0]], ![![-1044503960722196, 229949169208201524, -3494684598106265], ![785386101955250, 509525014403893217, 0]]]
    h := ![![![3207236991, -55520645599, 8412966895], ![-883531996, -301184214983, 0]], ![![-1474993488, 25533688919, -3869084685], ![406332383, 138513231787, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {729} * I179N1 =  Ideal.span {B.equivFun.symm ![15295, 222, -710]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E179RS1 


noncomputable def E181RS0 : RelationCertificate Table 3 ![![181, 0, 0], ![24, 1, 0]]
  ![2183, 285, 146] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![543, 0, 0], ![72, 3, 0]]
    hsu := by decide
    w := ![![6549, 855, 438], ![21309, 2781, 1425]]
    hw := by decide
    g := ![![![-300, -26, 11], ![94, 0, 0]], ![![-26, -9, 15], ![9, -8, 0]]]
    h := ![![![-899917, -10619380, -2308774], ![-177839, 83577648, 0]], ![![-2928085, -34553135, -7512245], ![-579010, 271943364, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N0 : Ideal.span {3} * I181N0 =  Ideal.span {B.equivFun.symm ![2183, 285, 146]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E181RS0 


noncomputable def E181RS1 : RelationCertificate Table 81 ![![181, 0, 0], ![59, 1, 0]]
  ![81889, 10689, 5476] ![![81, 0, 0], ![-4, 1, 0]] where
    su := ![![14661, 0, 0], ![4779, 81, 0]]
    hsu := by decide
    w := ![![6633009, 865809, 443556], ![553554, 72252, 37017]]
    hw := by decide
    g := ![![![266819920, -669432297, 669697001], ![-21440857, -10849091360, 0]], ![![88842629, -222899853, 222987990], ![-7139063, -3612405420, 0]]]
    h := ![![![3659808, 123856990, 10678246], ![1877279, -386551410, 0]], ![![305411, 10336415, 891147], ![156717, -32259430, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {81} * I181N1 =  Ideal.span {B.equivFun.symm ![81889, 10689, 5476]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E181RS1 


noncomputable def E181RS2 : RelationCertificate Table 27 ![![181, 0, 0], ![-83, 1, 0]]
  ![-160, 3, 5] ![![27, 0, 0], ![-4, 1, 0]] where
    su := ![![4887, 0, 0], ![-2241, 27, 0]]
    hsu := by decide
    w := ![![-4320, 81, 135], ![1431, -135, 0]]
    hw := by decide
    g := ![![![43222293, -111567577, 111957775], ![-10535419, -604571990, 0]], ![![-19733966, 50938317, -51116470], ![4810160, 276028940, 0]]]
    h := ![![![-1017, 58292, -3470], ![811, 125615, 0]], ![![375, -19319, 1150], ![-186, -41630, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N2 : Ideal.span {27} * I181N2 =  Ideal.span {B.equivFun.symm ![-160, 3, 5]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E181RS2 


noncomputable def E191RS1 : RelationCertificate Table 3 ![![191, 0, 0], ![89, 1, 0]]
  ![-262, -15, 17] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![573, 0, 0], ![267, 3, 0]]
    hsu := by decide
    w := ![![-786, -45, 51], ![2901, -96, -75]]
    hw := by decide
    g := ![![![-179450, 184629, -560907], ![121363, 336728, 0]], ![![-84945, 87650, -266130], ![57535, 159774, 0]]]
    h := ![![![15726, 944737, 53682], ![12330, -2050649, 0]], ![![-58248, -3490457, -198335], ![-45241, 7576392, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {3} * I191N1 =  Ideal.span {B.equivFun.symm ![-262, -15, 17]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E191RS1 
