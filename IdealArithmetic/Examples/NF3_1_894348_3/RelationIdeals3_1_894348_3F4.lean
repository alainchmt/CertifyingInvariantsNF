import IdealArithmetic.Examples.NF3_1_894348_3.PrimesBelow3_1_894348_3F4
import IdealArithmetic.Examples.NF3_1_894348_3.ClassGroupData3_1_894348_3

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 55 ![![197, 0, 0], ![59, 1, 0]]
  ![83, -48, 26] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![10835, 0, 0], ![3245, 55, 0]]
    hsu := by decide
    w := ![![4565, -2640, 1430], ![4400, 275, -440]]
    hw := by decide
    g := ![![![1791, 1418166, -2482625], ![25690, 19506303, 0]], ![![533, 422929, -740377], ![7706, 5817235, 0]]]
    h := ![![![128220, 2509, 40], ![-428123, -1122, 0]], ![![124022, 2448, 41], ![-414106, -1155, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {55} * I197N1 =  Ideal.span {B.equivFun.symm ![83, -48, 26]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E197RS1 


noncomputable def E211RS0 : RelationCertificate Table 55 ![![211, 0, 0], ![30, 1, 0]]
  ![-107, -13, -9] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![11605, 0, 0], ![1650, 55, 0]]
    hsu := by decide
    w := ![![-5885, -715, -495], ![-1210, -55, -55]]
    hw := by decide
    g := ![![![94981, 72205549, -126401264], ![1305944, 993152788, 0]], ![![13674, 10394629, -18196583], ![188012, 142973152, 0]]]
    h := ![![![-128957, -4427, -30], ![906994, 903, 0]], ![![-26542, -919, -8], ![186678, 241, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N0 : Ideal.span {55} * I211N0 =  Ideal.span {B.equivFun.symm ![-107, -13, -9]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E211RS0 


noncomputable def E211RS1 : RelationCertificate Table 55 ![![211, 0, 0], ![-28, 1, 0]]
  ![37391, 3449, 2227] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![11605, 0, 0], ![-1540, 55, 0]]
    hsu := by decide
    w := ![![2056505, 189695, 122485], ![255750, 23595, 15235]]
    hw := by decide
    g := ![![![43, -9096, 15914], ![-131, -125040, 0]], ![![-4, 1180, -2065], ![43, 16224, 0]]]
    h := ![![![554341, -20073, 85], ![4176020, -2244, 0]], ![![68966, -2471, 4], ![519542, -81, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {55} * I211N1 =  Ideal.span {B.equivFun.symm ![37391, 3449, 2227]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E211RS1 


noncomputable def E211RS2 : RelationCertificate Table 55 ![![211, 0, 0], ![-2, 1, 0]]
  ![-1121, 91, 8] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![11605, 0, 0], ![-110, 55, 0]]
    hsu := by decide
    w := ![![-61655, 5005, 440], ![5940, -1485, 605]]
    hw := by decide
    g := ![![![-369, -1243, 2092], ![36, -16611, 0]], ![![-12, 4, -12], ![49, 87, 0]]]
    h := ![![![-123351, 61679, -20], ![-13012970, 604, 0]], ![![11888, -5943, -3], ![1254130, 92, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N2 : Ideal.span {55} * I211N2 =  Ideal.span {B.equivFun.symm ![-1121, 91, 8]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E211RS2 


noncomputable def E223RS0 : RelationCertificate Table 55 ![![223, 0, 0], ![4, 1, 0]]
  ![579, -89, 23] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![12265, 0, 0], ![220, 55, 0]]
    hsu := by decide
    w := ![![31845, -4895, 1265], ![1870, 935, -715]]
    hw := by decide
    g := ![![![235, 1651, -2838], ![14, 22408, 0]], ![![16, 31, -51], ![6, 408, 0]]]
    h := ![![![573, 141, -2], ![-31800, 67, 0]], ![![30, 7, -1], ![-1664, 30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N0 : Ideal.span {55} * I223N0 =  Ideal.span {B.equivFun.symm ![579, -89, 23]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E223RS0 


noncomputable def E223RS1 : RelationCertificate Table 55 ![![223, 0, 0], ![63, 1, 0]]
  ![-149, 4, 7] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![12265, 0, 0], ![3465, 55, 0]]
    hsu := by decide
    w := ![![-8195, 220, 385], ![1870, -165, 0]]
    hw := by decide
    g := ![![![-7, -10660, 18662], ![-174, -146627, 0]], ![![-1, -3051, 5341], ![-40, -41964, 0]]]
    h := ![![![-300746, -5404, -70], ![1064543, 2231, 0]], ![![68482, 1213, 14], ![-242404, -446, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N1 : Ideal.span {55} * I223N1 =  Ideal.span {B.equivFun.symm ![-149, 4, 7]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E223RS1 


noncomputable def E223RS2 : RelationCertificate Table 55 ![![223, 0, 0], ![-67, 1, 0]]
  ![4881, -856, 262] ![![55, 0, 0], ![-4, 1, 0]] where
    su := ![![12265, 0, 0], ![-3685, 55, 0]]
    hsu := by decide
    w := ![![268455, -47080, 14410], ![28160, 8305, -7040]]
    hw := by decide
    g := ![![![-21253, -123, -4558], ![1597, 25812, 0]], ![![5357, -44, 1277], ![-337, -7515, 0]]]
    h := ![![![22475, -299, -3], ![74732, 133, 0]], ![![2350, 8, -5], ![7814, 141, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R223N2 : Ideal.span {55} * I223N2 =  Ideal.span {B.equivFun.symm ![4881, -856, 262]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E223RS2 


noncomputable def E227RS1 : RelationCertificate Table 605 ![![227, 0, 0], ![-12, 1, 0]]
  ![541, -16, -28] ![![605, 0, 0], ![-4, 1, 0]] where
    su := ![![137335, 0, 0], ![-7260, 605, 0]]
    hsu := by decide
    w := ![![327305, -9680, -16940], ![-7260, 605, 0]]
    hw := by decide
    g := ![![![18899, 1729315035, -3026309580], ![2858561, 261559613696, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![611, -39, -7], ![11513, 223, 0]], ![![-12, 13, -7], ![-226, 227, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {605} * I227N1 =  Ideal.span {B.equivFun.symm ![541, -16, -28]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E227RS1 


noncomputable def E233RS1 : RelationCertificate Table 5 ![![233, 0, 0], ![-52, 1, 0]]
  ![737, 68, 44] ![![5, 0, 0], ![1, 1, 0]] where
    su := ![![1165, 0, 0], ![-260, 5, 0]]
    hsu := by decide
    w := ![![3685, 340, 220], ![8745, 805, 520]]
    hw := by decide
    g := ![![![-213, 4138, 30008], ![790, -21436, 0]], ![![45, -929, -6729], ![-173, 4807, 0]]]
    h := ![![![208589, -4121, 15], ![934625, -493, 0]], ![![495033, -9850, 45], ![2218095, -1483, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {5} * I233N1 =  Ideal.span {B.equivFun.symm ![737, 68, 44]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E233RS1 


noncomputable def E251RS1 : RelationCertificate Table 3025 ![![251, 0, 0], ![-24, 1, 0]]
  ![18119, 1656, 1083] ![![3025, 0, 0], ![601, 1, 0]] where
    su := ![![759275, 0, 0], ![-72600, 3025, 0]]
    hsu := by decide
    w := ![![54809975, 5009400, 3276075], ![11086625, 1013375, 662475]]
    hw := by decide
    g := ![![![-7709743334732632, 122019529292232052553, 1421192670287799835], ![38805280511757425, -614158261088656357288, 0]], ![![738466451416719, -11687461551940133688, -136126854350561882], ![-3716906847812937, 58826247772921384724, 0]]]
    h := ![![![1429341925, -60052000, 144699], ![14948533544, -5188338, 0]], ![![289118515, -12146937, 29265], ![3023697650, -1049328, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N1 : Ideal.span {3025} * I251N1 =  Ideal.span {B.equivFun.symm ![18119, 1656, 1083]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E251RS1 


noncomputable def E257RS1 : RelationCertificate Table 275 ![![257, 0, 0], ![-117, 1, 0]]
  ![-131, -19, 8] ![![275, 0, 0], ![51, 1, 0]] where
    su := ![![70675, 0, 0], ![-32175, 275, 0]]
    hsu := by decide
    w := ![![-36025, -5225, 2200], ![-5225, -1100, 275]]
    hw := by decide
    g := ![![![-26, 37310, 5121], ![137, -201184, 0]], ![![-35, -16656, -2286], ![190, 89808, 0]]]
    h := ![![![-5724307, 55194, -375], ![-12573904, 13769, 0]], ![![-830009, 8097, -60], ![-1823182, 2203, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N1 : Ideal.span {275} * I257N1 =  Ideal.span {B.equivFun.symm ![-131, -19, 8]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E257RS1 
