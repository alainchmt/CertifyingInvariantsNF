import IdealArithmetic.Examples.NF3_1_614075_2.PrimesBelow3_1_614075_2F3
import IdealArithmetic.Examples.NF3_1_614075_2.ClassGroupData3_1_614075_2

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 8 ![![139, 0, 0], ![-39, 1, 0]]
  ![13, 7, 1] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![1112, 0, 0], ![-312, 8, 0]]
    hsu := by decide
    w := ![![104, 56, 8], ![-112, -24, 8]]
    hw := by decide
    g := ![![![57, -5, -251226], ![3, 2009818, 0]], ![![-17, 1, 70032], ![3, -560259, 0]]]
    h := ![![![4732, -121, 0], ![16865, 1, 0]], ![![-4982, 167, -1], ![-17756, 140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {8} * I139N1 =  Ideal.span {B.equivFun.symm ![13, 7, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E139RS1 


noncomputable def E149RS0 : RelationCertificate Table 16 ![![149, 0, 0], ![74, 1, 0]]
  ![6507, -495, 143] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![2384, 0, 0], ![1184, 16, 0]]
    hsu := by decide
    w := ![![104112, -7920, 2288], ![-16016, 1216, -352]]
    hw := by decide
    g := ![![![-10, -1, 4963099], ![5, -79409562, 0]], ![![-6, -1, 2500620], ![4, -40009909, 0]]]
    h := ![![![1643831, 42785, 279], ![-3309788, -41428, 0]], ![![-252897, -6588, -43], ![509198, 6385, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N0 : Ideal.span {16} * I149N0 =  Ideal.span {B.equivFun.symm ![6507, -495, 143]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E149RS0 


noncomputable def E149RS1 : RelationCertificate Table 4 ![![149, 0, 0], ![-74, 1, 0]]
  ![-545, -283, -25] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![596, 0, 0], ![-296, 4, 0]]
    hsu := by decide
    w := ![![-2180, -1132, -100], ![2800, 380, -308]]
    hw := by decide
    g := ![![![274983, -19678, 6115], ![-4919, -294, 0]], ![![-141110, 10097, -3136], ![2528, 143, 0]]]
    h := ![![![-162013, 2619, -6], ![-326208, 869, 0]], ![![208640, -3301, 6], ![420090, -971, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {4} * I149N1 =  Ideal.span {B.equivFun.symm ![-545, -283, -25]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E149RS1 


noncomputable def E151RS0 : RelationCertificate Table 2 ![![151, 0, 0], ![16, 1, 0]]
  ![43, 15, -1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![302, 0, 0], ![32, 2, 0]]
    hsu := by decide
    w := ![![86, 30, -2], ![112, 80, 14]]
    hw := by decide
    g := ![![![3301, -201, -154], ![-100, 453, 0]], ![![296, -18, -16], ![-9, 45, 0]]]
    h := ![![![941, 59, 0], ![-8878, -1, 0]], ![![1224, 76, 0], ![-11548, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N0 : Ideal.span {2} * I151N0 =  Ideal.span {B.equivFun.symm ![43, 15, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E151RS0 


noncomputable def E151RS1 : RelationCertificate Table 4 ![![151, 0, 0], ![25, 1, 0]]
  ![225, -17, 5] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![604, 0, 0], ![100, 4, 0]]
    hsu := by decide
    w := ![![900, -68, 20], ![-560, 40, -12]]
    hw := by decide
    g := ![![![-17, -7, 261972976], ![2, -1047891903, 0]], ![![-3, -2, 41639128], ![3, -166556512, 0]]]
    h := ![![![15375, 614, 0], ![-92856, 5, 0]], ![![-9590, -408, -1], ![57918, 148, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {4} * I151N1 =  Ideal.span {B.equivFun.symm ![225, -17, 5]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E151RS1 


noncomputable def E151RS2 : RelationCertificate Table 8 ![![151, 0, 0], ![-42, 1, 0]]
  ![-27, -9, 1] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![1208, 0, 0], ![-336, 8, 0]]
    hsu := by decide
    w := ![![-216, -72, 8], ![-112, -64, -8]]
    hw := by decide
    g := ![![![95, -8, 167701], ![6, -1341591, 0]], ![![-28, 2, -47755], ![1, 382035, 0]]]
    h := ![![![-117, 3, 0], ![-420, 1, 0]], ![![-98, 44, -1], ![-352, 150, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N2 : Ideal.span {8} * I151N2 =  Ideal.span {B.equivFun.symm ![-27, -9, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E151RS2 


noncomputable def E167RS1 : RelationCertificate Table 8 ![![167, 0, 0], ![-55, 1, 0]]
  ![2957, -225, 65] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![1336, 0, 0], ![-440, 8, 0]]
    hsu := by decide
    w := ![![23656, -1800, 520], ![-7280, 552, -160]]
    hw := by decide
    g := ![![![-19, -4, 48], ![7, -369, 0]], ![![5, 0, -13], ![4, 99, 0]]]
    h := ![![![104081, -1982, 2], ![315974, -269, 0]], ![![-31970, 630, -1], ![-97056, 147, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {8} * I167N1 =  Ideal.span {B.equivFun.symm ![2957, -225, 65]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E167RS1 


noncomputable def E173RS1 : RelationCertificate Table 8 ![![173, 0, 0], ![64, 1, 0]]
  ![331, 73, -25] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![1384, 0, 0], ![512, 8, 0]]
    hsu := by decide
    w := ![![2648, 584, -200], ![2800, 1256, 48]]
    hw := by decide
    g := ![![![-24823, 1858, -701], ![235, 1245, 0]], ![![-8830, 661, -252], ![83, 464, 0]]]
    h := ![![![6423, 110, 0], ![-17357, -25, 0]], ![![6806, 105, 0], ![-18392, 6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R173N1 : Ideal.span {8} * I173N1 =  Ideal.span {B.equivFun.symm ![331, 73, -25]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E173RS1 


noncomputable def E179RS0 : RelationCertificate Table 2 ![![179, 0, 0], ![48, 1, 0]]
  ![32999, -2509, 725] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![358, 0, 0], ![96, 2, 0]]
    hsu := by decide
    w := ![![65998, -5018, 1450], ![-81200, 6174, -1784]]
    hw := by decide
    g := ![![![333, 62, 38944], ![31, -77935, 0]], ![![104, 22, 10719], ![11, -21450, 0]]]
    h := ![![![1722637, 39756, 85], ![-6423313, -14490, 0]], ![![-2119496, -48983, -106], ![7903108, 18082, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N0 : Ideal.span {2} * I179N0 =  Ideal.span {B.equivFun.symm ![32999, -2509, 725]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E179RS0 


noncomputable def E179RS1 : RelationCertificate Table 32 ![![179, 0, 0], ![50, 1, 0]]
  ![-233, 21, -5] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![5728, 0, 0], ![1600, 32, 0]]
    hsu := by decide
    w := ![![-7456, 672, -160], ![-3168, 288, -64]]
    hw := by decide
    g := ![![![-1353405, 108271509, 6772256], ![2706806, -216712195, 0]], ![![-370485, 29638557, 1853857], ![740969, -59323425, 0]]]
    h := ![![![-249927, -5547, -11], ![894734, 1964, 0]], ![![-106281, -2375, -5], ![380484, 893, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {32} * I179N1 =  Ideal.span {B.equivFun.symm ![-233, 21, -5]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E179RS1 


noncomputable def E181RS1 : RelationCertificate Table 32 ![![181, 0, 0], ![6, 1, 0]]
  ![-363, -145, 1] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![5792, 0, 0], ![192, 32, 0]]
    hsu := by decide
    w := ![![-11616, -4640, 32], ![-5920, -2720, -128]]
    hw := by decide
    g := ![![![-70281, 5560679, 347788], ![138670, -11129881, 0]], ![![-1937, 153616, 9608], ![3837, -307469, 0]]]
    h := ![![![-65523, -10939, -3], ![1976550, 544, 0]], ![![-33401, -5579, -2], ![1007566, 358, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R181N1 : Ideal.span {32} * I181N1 =  Ideal.span {B.equivFun.symm ![-363, -145, 1]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E181RS1 


noncomputable def E191RS1 : RelationCertificate Table 8 ![![191, 0, 0], ![41, 1, 0]]
  ![-3, -1, 1] ![![8, 0, 0], ![0, 1, 0]] where
    su := ![![1528, 0, 0], ![328, 8, 0]]
    hsu := by decide
    w := ![![-24, -8, 8], ![-112, -40, 0]]
    hw := by decide
    g := ![![![25, -3, 191], ![5, -1523, 0]], ![![5, -1, 41], ![4, -327, 0]]]
    h := ![![![-73, -2, 0], ![340, 1, 0]], ![![-122, -44, -1], ![568, 191, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R191N1 : Ideal.span {8} * I191N1 =  Ideal.span {B.equivFun.symm ![-3, -1, 1]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E191RS1 


noncomputable def E193RS1 : RelationCertificate Table 2 ![![193, 0, 0], ![-74, 1, 0]]
  ![-85, -37, -1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![386, 0, 0], ![-148, 2, 0]]
    hsu := by decide
    w := ![![-170, -74, -2], ![112, -48, -38]]
    hw := by decide
    g := ![![![-15453, 940, -50], ![470, -579, 0]], ![![6122, -373, 22], ![-185, 225, 0]]]
    h := ![![![-2781, 111, -1], ![-7252, 192, 0]], ![![1968, 40, -1], ![5132, 174, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {2} * I193N1 =  Ideal.span {B.equivFun.symm ![-85, -37, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E193RS1 
