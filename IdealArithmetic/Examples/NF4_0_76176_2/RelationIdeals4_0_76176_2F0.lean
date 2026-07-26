import IdealArithmetic.Examples.NF4_0_76176_2.PrimesBelow4_0_76176_2F0
import IdealArithmetic.Examples.NF4_0_76176_2.ClassGroupData4_0_76176_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 8 ![![2, 0, 0, 0], ![-1, 1, 0, -1]]
  ![2, -2, -2, 5] ![![8, 0, 0, 0], ![-4, 3, 0, -1]] where
    su := ![![16, 0, 0, 0], ![-8, 8, 0, -8]]
    hsu := by decide
    w := ![![16, -16, -16, 40], ![8, -8, -16, 32]]
    hw := by decide
    g := ![![![-711, 432, 2166, -3427], ![954, -1573, 1, 0]], ![![-487, 297, 1485, -2349], ![649, -1080, 0, 0]]]
    h := ![![![-36374, 35483, -280, -35198], ![-71292, 27, 45, 0]], ![![-36422, 35531, -280, -35246], ![-71387, 27, 45, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {8} * I2N0 =  Ideal.span {B.equivFun.symm ![2, -2, -2, 5]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0, 0], ![0, 0, -1, 1]]
  ![1, 0, 0, 0] ![![2, 0, 0, 0], ![0, -1, 0, 0]] where
    su := ![![2, 0, 0, 0], ![0, 0, -1, 1]]
    hsu := by decide
    w := ![![2, 0, 0, 0], ![0, -1, 0, 0]]
    hw := by decide
    g := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![8, -12, -6, 18], ![-9, 5, 1, 0]]]
    h := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![-8, -7, -34, 44], ![-45, 1, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 6 ![![3, 0, 0, 0], ![-1, 1, -1, 1]]
  ![-1, 0, -1, 1] ![![6, 0, 0, 0], ![-2, 0, -3, 4]] where
    su := ![![18, 0, 0, 0], ![-6, 6, -6, 6]]
    hsu := by decide
    w := ![![-6, 0, -6, 6], ![-36, 6, 0, 0]]
    hw := by decide
    g := ![![![-71941, 29544, 26946, -67875], ![-34740, -16115, -424, 0]], ![![17985, -7385, -6733, 16963], ![8689, 4028, 106, 0]]]
    h := ![![![-5903, 3605, 4372, -8633], ![-1164, -1583, 17, 0]], ![![-11840, 7231, 8769, -17315], ![-2336, -3175, 34, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {6} * I3N0 =  Ideal.span {B.equivFun.symm ![-1, 0, -1, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 8 ![![3, 0, 0, 0], ![1, -1, 0, 0]]
  ![-1, 0, -1, 2] ![![24, 0, 0, 0], ![18, -16, -13, 34]] where
    su := ![![24, 0, 0, 0], ![8, -8, 0, 0]]
    hsu := by decide
    w := ![![-24, 0, -24, 48], ![-32, -16, -24, 24]]
    hw := by decide
    g := ![![![305555233, 66103008, 226800007, -311198841], ![-378617265, 129565368, -138, 0]], ![![162651, 35198, 120742, -165682], ![-201541, 68973, 0, 0]]]
    h := ![![![-806, 819, 353, -803], ![1311, -111, -69, 0]], ![![-2412, 2454, 1059, -2414], ![3920, -339, -207, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {8} * I3N1 =  Ideal.span {B.equivFun.symm ![-1, 0, -1, 2]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 6 ![![5, 0, 0, 0], ![-2, -1, 0, 0]]
  ![2, 0, 2, -5] ![![6, 0, 0, 0], ![-4, 4, -1, -1]] where
    su := ![![30, 0, 0, 0], ![-12, -6, 0, 0]]
    hsu := by decide
    w := ![![12, 0, 12, -30], ![-18, -18, -42, 60]]
    hw := by decide
    g := ![![![45420420, -45408536, 11354034, 11350149], ![68112425, -537, -651, 0]], ![![-9001121, 8998768, -2250088, -2249270], ![-13498094, 110, 129, 0]]]
    h := ![![![14, 10, 2, -1], ![34, 8, 0, 0]], ![![-23, -13, -2, 2], ![-56, -3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {6} * I5N0 =  Ideal.span {B.equivFun.symm ![2, 0, 2, -5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 6 ![![5, 0, 0, 0], ![-4, 1, 2, -4]]
  ![-4, 0, -4, 7] ![![6, 0, 0, 0], ![-4, 4, -1, -1]] where
    su := ![![30, 0, 0, 0], ![-24, 6, 12, -24]]
    hsu := by decide
    w := ![![-24, 0, -24, 42], ![-126, 42, 66, -114]]
    hw := by decide
    g := ![![![11539889925, -2089901325, -38935159954, 59277469245], ![-32067732429, 7340873377, -55, -666871256]], ![![-11780015429, 2133388621, 39745335272, -60510933825], ![32735008134, -7493624624, 55, 680747708]]]
    h := ![![![116, 94, 8, -61], ![-22, 0, 0, -112]], ![![819, 658, 61, -435], ![-147, 0, 0, -784]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {6} * I5N1 =  Ideal.span {B.equivFun.symm ![-4, 0, -4, 7]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E13RS0 : RelationCertificate Table 12 ![![13, 0, 0, 0], ![1, 1, 0, -1]]
  ![-10, 6, 2, -5] ![![12, 0, 0, 0], ![-10, 6, 3, -10]] where
    su := ![![156, 0, 0, 0], ![12, 12, 0, -12]]
    hsu := by decide
    w := ![![-120, 72, 24, -60], ![-36, 36, 132, -240]]
    hw := by decide
    g := ![![![105973014542, 46394986787, 180751604215, -283278093105], ![216139626607, -74143116327, 17061, 0]], ![![12477934, 5462835, 21282830, -33354941], ![25449645, -8730077, 2, 0]]]
    h := ![![![21072, -29636, -29938, 59625], ![-5242, 43464, -220, 0]], ![![7662, -10776, -10885, 21679], ![-1905, 15804, -80, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {12} * I13N0 =  Ideal.span {B.equivFun.symm ![-10, 6, 2, -5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 24 ![![13, 0, 0, 0], ![4, 1, 0, -1]]
  ![2, -6, -10, 19] ![![24, 0, 0, 0], ![-28, 19, 0, -9]] where
    su := ![![312, 0, 0, 0], ![96, 24, 0, -24]]
    hsu := by decide
    w := ![![48, -144, -240, 456], ![-696, 168, 120, -216]]
    hw := by decide
    g := ![![![-2437917373001, -1836298110274, -43182443685376, 67853899147850], ![-24054711249203, 11388690462635, -67382321, 0]], ![![-562507844730, -423694463050, -9963612219550, 15656129690564], ![-5550214264998, 2627746041538, -15547321, 0]]]
    h := ![![![-257107514, 502075007, 377561858, -753783670], ![17494519, -545373700, 4928, 0]], ![![-449988201, 878729010, 660806759, -1319268176], ![30618805, -954510150, 8624, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {24} * I13N1 =  Ideal.span {B.equivFun.symm ![2, -6, -10, 19]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 12 ![![13, 0, 0, 0], ![-5, 1, 0, -1]]
  ![-4, 6, 8, -17] ![![12, 0, 0, 0], ![-10, 6, 3, -10]] where
    su := ![![156, 0, 0, 0], ![-60, 12, 0, -12]]
    hsu := by decide
    w := ![![-48, 72, 96, -204], ![-60, -36, 12, -60]]
    hw := by decide
    g := ![![![-2555223649, -1118669315, -4358208905, 6830289858], ![-5211442039, 1787704113, 4511, 0]], ![![1177056247, 515311721, 2007596087, -3146352890], ![2400635421, -823500631, -2078, 0]]]
    h := ![![![27139541, -15819297, -51967114, 102430942], ![-19534455, 75064528, -2754, 0]], ![![-31665710, 18457545, 60633880, -119513765], ![22792299, -87583342, 3213, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {12} * I13N2 =  Ideal.span {B.equivFun.symm ![-4, 6, 8, -17]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS2 


noncomputable def E13RS3 : RelationCertificate Table 24 ![![13, 0, 0, 0], ![-8, 1, 0, -1]]
  ![8, -6, -4, 7] ![![24, 0, 0, 0], ![-28, 19, 0, -9]] where
    su := ![![312, 0, 0, 0], ![-192, 24, 0, -24]]
    hsu := by decide
    w := ![![192, -144, -96, 168], ![-408, 72, -264, 384]]
    hw := by decide
    g := ![![![-9880695520810420, -7441465557106790, -174973675539286754, 274941560510848707], ![-97466767316665645, 46146903418469061, -16053427, 0]], ![![6840306714150870, 5151652199603923, 121132526052464166, -190339293261332442], ![67475268464510160, -31947039823845706, 11113627, 0]]]
    h := ![![![300502912, 22488596, -720535708, 1418577365], ![-292316300, 1040773800, -11818, 0]], ![![-561466689, -42018223, 1346265841, -2650503268], ![546170659, -1944606216, 22081, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N3 : Ideal.span {24} * I13N3 =  Ideal.span {B.equivFun.symm ![8, -6, -4, 7]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E13RS3 


noncomputable def E23RS0 : RelationCertificate Table 12 ![![23, 0, 0, 0], ![6, 1, 0, -1]]
  ![-5, 0, -5, 8] ![![12, 0, 0, 0], ![0, -1, 2, -5]] where
    su := ![![276, 0, 0, 0], ![72, 12, 0, -12]]
    hsu := by decide
    w := ![![-60, 0, -60, 96], ![72, -24, -60, 120]]
    hw := by decide
    g := ![![![-6685973006827, -35427972151163, -19404691945919, 56869196076467], ![-23977282676917, 40115838153430, 28118, 0]], ![![-2163116273562, -11462029987444, -6278009930466, 18398920152956], ![-7757382553183, 12978697677761, 9097, 0]]]
    h := ![![![-2206735, 5117750, 3277670, -6574684], ![-67285, -8407185, 19875, 0]], ![![1853658, -4298928, -2753254, 5522758], ![56545, 7062063, -16695, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {12} * I23N0 =  Ideal.span {B.equivFun.symm ![-5, 0, -5, 8]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 12 ![![23, 0, 0, 0], ![-10, 1, 0, -1]]
  ![-1, 0, -1, 4] ![![12, 0, 0, 0], ![0, -1, 2, -5]] where
    su := ![![276, 0, 0, 0], ![-120, 12, 0, -12]]
    hsu := by decide
    w := ![![-12, 0, -12, 48], ![24, 72, 60, -120]]
    hw := by decide
    g := ![![![-33187494583, -175855567813, -96320022413, 282284425599], ![-119017217074, 199124964258, -805, 0]], ![![12987785944, 68820334303, 37694434271, -110470818631], ![46576885627, -77926714397, 315, 0]]]
    h := ![![![-50023, -22104, 93795, -186312], ![28898, -239690, 38, 0]], ![![344732, 152313, -646329, 1283855], ![-199063, 1651672, -262, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {12} * I23N1 =  Ideal.span {B.equivFun.symm ![-1, 0, -1, 4]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E23RS1 
