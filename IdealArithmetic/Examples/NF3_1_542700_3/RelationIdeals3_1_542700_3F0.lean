import IdealArithmetic.Examples.NF3_1_542700_3.PrimesBelow3_1_542700_3F0
import IdealArithmetic.Examples.NF3_1_542700_3.ClassGroupData3_1_542700_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 867 ![![2, 0, 0], ![0, 1, 0]]
  ![-2676, -7, -89] ![![867, 0, 0], ![-244, 1, 1]] where
    su := ![![1734, 0, 0], ![0, 867, 0]]
    hsu := by decide
    w := ![![-2320092, -6069, -77163], ![651984, 1734, 21675]]
    hw := by decide
    g := ![![![366376, -10924439, 199486], ![-114881, -34567896, 0]], ![![592003, -17653260, 322358], ![-185781, -55859716, 0]]]
    h := ![![![-1338, -6, -7], ![5, -15, 0]], ![![376, 0, 0], ![2, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {867} * I2N0 =  Ideal.span {B.equivFun.symm ![-2676, -7, -89]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 104907 ![![3, 0, 0], ![1, 1, 0]]
  ![-2449, -86, -20] ![![104907, 0, 0], ![-15850, 1, 1]] where
    su := ![![314721, 0, 0], ![104907, 104907, 0]]
    hsu := by decide
    w := ![![-256917243, -9022002, -2098140], ![38815590, 1363791, 314721]]
    hw := by decide
    g := ![![![-1963541162247, 3196588817562360, -1006485744398], ![327125111486, 21117414572489900, 0]], ![![2103943871, -3425134944979, 1078446334], ![-350410008, -22627243830184, 0]]]
    h := ![![![-1336, -570, -115], ![1559, 65, 0]], ![![200, 84, 16], ![-230, -9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {104907} * I3N0 =  Ideal.span {B.equivFun.symm ![-2449, -86, -20]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 867 ![![5, 0, 0], ![20, 0, 1]]
  ![35, -16, 3] ![![867, 0, 0], ![-244, 1, 1]] where
    su := ![![4335, 0, 0], ![17340, 0, 867]]
    hsu := by decide
    w := ![![30345, -13872, 2601], ![-8670, 4335, -867]]
    hw := by decide
    g := ![![![155, -850, 15], ![440, -2688, 0]], ![![336, -3390, 61], ![752, -10724, 0]]]
    h := ![![![6495, 27728, -138331], ![-1622, 0, -69328]], ![![-2038, -8665, 43228], ![509, 0, 21665]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {867} * I5N0 =  Ideal.span {B.equivFun.symm ![35, -16, 3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 14739 ![![7, 0, 0], ![22, 2, 1]]
  ![181, -380, -1] ![![14739, 0, 0], ![-5700, 3, 0]] where
    su := ![![103173, 0, 0], ![324258, 29478, 14739]]
    hsu := by decide
    w := ![![2667759, -5600820, -14739], ![-1031730, 2166633, 0]]
    hw := by decide
    g := ![![![3087, 18651540, -49083], ![7982, 48228960, 0]], ![![4442, 59683563, -157062], ![11485, 154329135, 0]]]
    h := ![![![7, -56, -1], ![6, 0, 0]], ![![-10, 21, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {14739} * I7N0 =  Ideal.span {B.equivFun.symm ![181, -380, -1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 14739 ![![7, 0, 0], ![-3, 1, 0]]
  ![207, 54, 26] ![![14739, 0, 0], ![-5700, 3, 0]] where
    su := ![![103173, 0, 0], ![-44217, 14739, 0]]
    hsu := by decide
    w := ![![3050973, 795906, 383214], ![-1179120, -309519, -147390]]
    hw := by decide
    g := ![![![-410338319, -5992585462592, 15769962312], ![-1061048506, -15495564967770, 0]], ![![141667211, 2068882792678, -5444428598], ![366321583, 5349695540394, 0]]]
    h := ![![![10771524, -3921312, 551373], ![25133487, -771917, 0]], ![![-4162316, 1515288, -213095], ![-9712044, 298331, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {14739} * I7N1 =  Ideal.span {B.equivFun.symm ![207, 54, 26]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 121 ![![11, 0, 0], ![24, 1, 1]]
  ![981, 1, 34] ![![121, 0, 0], ![39, 1, 0]] where
    su := ![![1331, 0, 0], ![2904, 121, 121]]
    hsu := by decide
    w := ![![118701, 121, 4114], ![38599, 0, 1331]]
    hw := by decide
    g := ![![![-27212, 11261457, 1443866], ![84427, -34941557, 0]], ![![-60644, 25117721, 3220420], ![188152, -77934164, 0]]]
    h := ![![![15, -3, 0], ![34, 0, 0]], ![![5, -1, 0], ![11, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {121} * I11N0 =  Ideal.span {B.equivFun.symm ![981, 1, 34]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![-5, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![-5, 1, 0]] where
    su := ![![11, 0, 0], ![-5, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![-5, 1, 0]]
    hw := by decide
    g := ![![![56, -11, 0], ![121, 0, 0]], ![![-20, 9, -5], ![-43, 11, 0]]]
    h := ![![![56, -11, 0], ![121, 0, 0]], ![![-20, 9, -5], ![-43, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 162129 ![![13, 0, 0], ![19, -4, 1]]
  ![-19241, -320, -518] ![![162129, 0, 0], ![23778, 3, 0]] where
    su := ![![2107677, 0, 0], ![3080451, -648516, 162129]]
    hsu := by decide
    w := ![![-3119524089, -51881280, -83982822], ![-457528038, -7620063, -12321804]]
    hw := by decide
    g := ![![![223977, -87105465471, -54949196], ![-1527175, 593923879886, 0]], ![![335277, -127502001598, -80432754], ![-2286068, 869365464881, 0]]]
    h := ![![![-514, -228, 11], ![-661, 0, 0]], ![![-87, -31, 1], ![-89, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {162129} * I13N0 =  Ideal.span {B.equivFun.symm ![-19241, -320, -518]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 1783419 ![![13, 0, 0], ![-6, 1, 0]]
  ![1743, -1895, 1999] ![![1783419, 0, 0], ![-786867, 3, 0]] where
    su := ![![23184447, 0, 0], ![-10700514, 1783419, 0]]
    hsu := by decide
    w := ![![3108499317, -3379579005, 3565054581], ![-1371449211, 1490938284, -1572975558]]
    hw := by decide
    g := ![![![-13370055786356, -21521119715303462879, 410255857381637], ![-30302975624149, -48777206061046778415, 0]], ![![4953427865091, 7973288435184648679, -151994335164714], ![11226849479941, 18071305681674605125, 0]]]
    h := ![![![22005137733, -4154070710, 405456513], ![47677798131, -1054186534, 0]], ![![-9708482047, 1832741977, -178884719], ![-21035044307, 465100093, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {1783419} * I13N1 =  Ideal.span {B.equivFun.symm ![1743, -1895, 1999]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 162129 ![![17, 0, 0], ![3, 1, 0]]
  ![-90777, -184, -3000] ![![162129, 0, 0], ![23778, 3, 0]] where
    su := ![![2756193, 0, 0], ![486387, 162129, 0]]
    hsu := by decide
    w := ![![-14717584233, -29831736, -486387000], ![-2158585506, -4377483, -71336760]]
    hw := by decide
    g := ![![![17728790991, -6673389049430316, -4209808889520], ![-120882797316, 45502140363265880, 0]], ![![3136429175, -1180600904800192, -744764638655], ![-21385571777, 8049863073366433, 0]]]
    h := ![![![-89571, -28975, -1655], ![477310, 5027, 0]], ![![-13140, -4252, -245], ![70022, 745, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {162129} * I17N0 =  Ideal.span {B.equivFun.symm ![-90777, -184, -3000]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 8268579 ![![17, 0, 0], ![4, 1, 0]]
  ![2617, -1667, 1017] ![![140565843, 0, 0], ![-32578257, 3, 3]] where
    su := ![![140565843, 0, 0], ![33074316, 8268579, 0]]
    hsu := by decide
    w := ![![367860811131, -234323260281, 142955462331], ![-85257318069, 54308026872, -33132196053]]
    hw := by decide
    g := ![![![-628152227269767097141, 722661621445347233240311678, -332734022190505860297], ![161007027583880861754, 3118069189397872006496363497, 0]], ![![-140410562018463886419, 161536200957768687971206989, -74375874239112430761], ![35989822610753895745, 696980490220890304629160663, 0]]]
    h := ![![![946840469117, 254545790158, 22294595017], ![-4024071982625, -75801619600, 0]], ![![-219444622219, -58994843053, -5167110281], ![932639641853, 17568174154, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {8268579} * I17N1 =  Ideal.span {B.equivFun.symm ![2617, -1667, 1017]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 8268579 ![![17, 0, 0], ![-7, 1, 0]]
  ![-64457, -367, -3634] ![![8268579, 0, 0], ![1645068, 3, 0]] where
    su := ![![140565843, 0, 0], ![-57880053, 8268579, 0]]
    hsu := by decide
    w := ![![-532967796603, -3034568493, -30048016086], ![-106036257096, -603606267, -5978182617]]
    hw := by decide
    g := ![![![8906617660690241, -128271012998638688525924, -1169596147381034683], ![-44767190019021981, 644726542847715225208352, 0]], ![![-3929390144956753, 56590152793555625335632, 515998300315513928], ![19750230893431982, -284438180668303455951216, 0]]]
    h := ![![![-201136, 30716, -2032], ![-479265, 6182, 0]], ![![-40012, 6110, -404], ![-95340, 1229, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {8268579} * I17N2 =  Ideal.span {B.equivFun.symm ![-64457, -367, -3634]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E17RS2 


noncomputable def E31RS1 : RelationCertificate Table 1783419 ![![31, 0, 0], ![3, 1, 0]]
  ![85009, 1029, 2679] ![![1783419, 0, 0], ![-786867, 3, 0]] where
    su := ![![55285989, 0, 0], ![5350257, 1783419, 0]]
    hsu := by decide
    w := ![![151606665771, 1835138151, 4777779501], ![-66890696433, -809672226, -2108001258]]
    hw := by decide
    g := ![![![105477117770556, 169781314127916839254, -3236531347641704], ![239061869283179, 384806099965321340396, 0]], ![![13210679571096, 21264579136852996082, -405365439208342], ![29941752481683, 48195761748500138749, 0]]]
    h := ![![![395835080644, 133316342325, 2285527294], ![-4090295804985, -14170268687, 0]], ![![-174647229700, -58820784212, -1008402317], ![1804688027731, 6252094129, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {1783419} * I31N1 =  Ideal.span {B.equivFun.symm ![85009, 1029, 2679]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E31RS1 
