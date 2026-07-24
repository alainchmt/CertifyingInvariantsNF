import IdealArithmetic.Examples.NF3_1_662796_2.PrimesBelow3_1_662796_2F1
import IdealArithmetic.Examples.NF3_1_662796_2.ClassGroupData3_1_662796_2

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 17 ![![41, 0, 0], ![-17, 1, 0]]
  ![-238, -56, -9] ![![17, 0, 0], ![5, 1, 0]] where
    su := ![![697, 0, 0], ![-289, 17, 0]]
    hsu := by decide
    w := ![![-4046, -952, -153], ![-5355, -1258, -204]]
    hw := by decide
    g := ![![![30, -36, -18], ![17, 100, 0]], ![![-20, 5, 3], ![10, -16, 0]]]
    h := ![![![-46507, -750699, 140751], ![1003, -1923600, 0]], ![![-61568, -993603, 186294], ![1297, -2546022, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {17} * I41N0 =  Ideal.span {B.equivFun.symm ![-238, -56, -9]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 119 ![![41, 0, 0], ![-13, 1, 0]]
  ![-153, -25, 6] ![![119, 0, 0], ![-46, 1, 0]] where
    su := ![![4879, 0, 0], ![-1547, 119, 0]]
    hsu := by decide
    w := ![![-18207, -2975, 714], ![9877, 1428, -357]]
    hw := by decide
    g := ![![![222, 8954, -597], ![60, 23680, 0]], ![![5, -1801, 120], ![117, -4760, 0]]]
    h := ![![![394467, 4767250, -1191759], ![-8775, 16287375, 0]], ![![-214166, -2588385, 647067], ![4797, -8843250, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {119} * I41N1 =  Ideal.span {B.equivFun.symm ![-153, -25, 6]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 833 ![![41, 0, 0], ![-11, 1, 0]]
  ![-255, -23, -4] ![![833, 0, 0], ![192, 1, 0]] where
    su := ![![34153, 0, 0], ![-9163, 833, 0]]
    hsu := by decide
    w := ![![-212415, -19159, -3332], ![-50813, -4998, -833]]
    hw := by decide
    g := ![![![9080, -1774507, -27583], ![495, 7658880, 0]], ![![-2431, 432319, 6720], ![829, -1865920, 0]]]
    h := ![![![2881, 29007, -8702], ![-50, 118926, 0]], ![![697, 6936, -2081], ![18, 28440, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {833} * I41N2 =  Ideal.span {B.equivFun.symm ![-255, -23, -4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E41RS2 


noncomputable def E47RS1 : RelationCertificate Table 119 ![![47, 0, 0], ![8, 1, 0]]
  ![8, -4, -1] ![![119, 0, 0], ![-43, -2, 1]] where
    su := ![![5593, 0, 0], ![952, 119, 0]]
    hsu := by decide
    w := ![![952, -476, -119], ![-952, -119, 0]]
    hw := by decide
    g := ![![![-10138010, -692903, 139521], ![3676187, 2897026, 0]], ![![-1917965, -131088, 26395], ![695596, 548086, 0]]]
    h := ![![![-32, 218, 73], ![46, -1144, 0]], ![![14, -199, -66], ![46, 1034, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {119} * I47N1 =  Ideal.span {B.equivFun.symm ![8, -4, -1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 833 ![![53, 0, 0], ![-13, 1, 0]]
  ![-1625, -381, -62] ![![833, 0, 0], ![314, -2, 1]] where
    su := ![![44149, 0, 0], ![-10829, 833, 0]]
    hsu := by decide
    w := ![![-1353625, -317373, -51646], ![-610589, -143276, -23324]]
    hw := by decide
    g := ![![![-1336539846, -1257714526, 23270189], ![-500761306, 2697615148, 0]], ![![326899949, 307620636, -5691587], ![122480599, -659801620, 0]]]
    h := ![![![-2325, -27717, 6926], ![60, -122380, 0]], ![![-1047, -12502, 3124], ![34, -55200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {833} * I53N1 =  Ideal.span {B.equivFun.symm ![-1625, -381, -62]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E53RS1 


noncomputable def E59RS1 : RelationCertificate Table 833 ![![59, 0, 0], ![-19, 1, 0]]
  ![3468, 205, -73] ![![833, 0, 0], ![192, 1, 0]] where
    su := ![![49147, 0, 0], ![-15827, 833, 0]]
    hsu := by decide
    w := ![![2888844, 170765, -60809], ![631414, 37485, -13328]]
    hw := by decide
    g := ![![![2181649955, -420947862905, -6543231076], ![-2485681, 1816837162101, 0]], ![![-693886567, 133884924962, 2081112838], ![790863, -577855664685, 0]]]
    h := ![![![-88925126, -1608629805, 268101091], ![1372048, -5272654814, 0]], ![![-19436179, -351594968, 58598314], ![299905, -1152433514, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {833} * I59N1 =  Ideal.span {B.equivFun.symm ![3468, 205, -73]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E59RS1 


noncomputable def E61RS1 : RelationCertificate Table 17 ![![61, 0, 0], ![26, 1, 0]]
  ![-328, -9, 5] ![![17, 0, 0], ![-43, -2, 1]] where
    su := ![![1037, 0, 0], ![442, 17, 0]]
    hsu := by decide
    w := ![![-5576, -153, 85], ![3485, 272, -85]]
    hw := by decide
    g := ![![![4, -21, -7], ![46, 0, 0]], ![![3, -15, -5], ![33, 0, 0]]]
    h := ![![![-905, 23506, 2612], ![68, -53109, 0]], ![![547, -14678, -1631], ![0, 33162, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {17} * I61N1 =  Ideal.span {B.equivFun.symm ![-328, -9, 5]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E61RS1 


noncomputable def E71RS0 : RelationCertificate Table 17 ![![71, 0, 0], ![13, 1, 0]]
  ![51, -14, 2] ![![17, 0, 0], ![5, 1, 0]] where
    su := ![![1207, 0, 0], ![221, 17, 0]]
    hsu := by decide
    w := ![![867, -238, 34], ![1207, 119, -34]]
    hw := by decide
    g := ![![![513665, -3032354, -1516978], ![-27292, 8596204, 0]], ![![98069, -578971, -289638], ![-5210, 1641280, 0]]]
    h := ![![![-9667, 134920, 28912], ![166, -684250, 0]], ![![-13005, 181615, 38918], ![182, -921060, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N0 : Ideal.span {17} * I71N0 =  Ideal.span {B.equivFun.symm ![51, -14, 2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E71RS0 


noncomputable def E71RS1 : RelationCertificate Table 119 ![![71, 0, 0], ![-12, 1, 0]]
  ![-578, -26, 11] ![![119, 0, 0], ![-46, 1, 0]] where
    su := ![![8449, 0, 0], ![-1428, 119, 0]]
    hsu := by decide
    w := ![![-68782, -3094, 1309], ![31773, 1428, -595]]
    hw := by decide
    g := ![![![47458660, 2141693428, -142779367], ![-347852, 5663581557, 0]], ![![-7186600, -324314663, 21620948], ![52730, -857630937, 0]]]
    h := ![![![13182, 145419, -39659], ![-175, 938600, 0]], ![![-6084, -67175, 18320], ![112, -433575, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {119} * I71N1 =  Ideal.span {B.equivFun.symm ![-578, -26, 11]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E71RS1 


noncomputable def E71RS2 : RelationCertificate Table 833 ![![71, 0, 0], ![-1, 1, 0]]
  ![7684, 288, -131] ![![833, 0, 0], ![192, 1, 0]] where
    su := ![![59143, 0, 0], ![-833, 833, 0]]
    hsu := by decide
    w := ![![6400772, 239904, -109123], ![1413601, 53312, -24157]]
    hw := by decide
    g := ![![![14558, -2812720, -43721], ![72, 12139875, 0]], ![![-69, 6690, 104], ![150, -28875, 0]]]
    h := ![![![-447717658, -88794, 1343419691], ![6304662, -31794266064, 0]], ![![-98877451, -19610, 296691257], ![1392374, -7021693092, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N2 : Ideal.span {833} * I71N2 =  Ideal.span {B.equivFun.symm ![7684, 288, -131]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E71RS2 


noncomputable def E73RS1 : RelationCertificate Table 17 ![![73, 0, 0], ![-28, 1, 0]]
  ![612, 26, -11] ![![17, 0, 0], ![5, 1, 0]] where
    su := ![![1241, 0, 0], ![-476, 17, 0]]
    hsu := by decide
    w := ![![10404, 442, -187], ![-2125, -68, 34]]
    hw := by decide
    g := ![![![-1482525, 8751445, 4378040], ![78758, -24808896, 0]], ![![549636, -3244585, -1623151], ![-29183, 9197856, 0]]]
    h := ![![![131406, 3563633, -395957], ![-1533, 9634950, 0]], ![![-26836, -728456, 80939], ![379, -1969515, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {17} * I73N1 =  Ideal.span {B.equivFun.symm ![612, 26, -11]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E73RS1 


noncomputable def E79RS1 : RelationCertificate Table 119 ![![79, 0, 0], ![-10, 1, 0]]
  ![289, 69, 12] ![![119, 0, 0], ![-46, 1, 0]] where
    su := ![![9401, 0, 0], ![-1190, 119, 0]]
    hsu := by decide
    w := ![![34391, 8211, 1428], ![-7735, -1904, -357]]
    hw := by decide
    g := ![![![67203364, 3032724283, -202181343], ![-492623, 8019859934, 0]], ![![-7639909, -344771976, 22984767], ![56090, -911729090, 0]]]
    h := ![![![-2426089, -21869716, 7289778], ![30283, -191964150, 0]], ![![545612, 4918279, -1639398], ![-6740, 43170813, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {119} * I79N1 =  Ideal.span {B.equivFun.symm ![289, 69, 12]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS1 
