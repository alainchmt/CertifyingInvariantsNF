import IdealArithmetic.Examples.NF3_1_662796_2.PrimesBelow3_1_662796_2F4
import IdealArithmetic.Examples.NF3_1_662796_2.ClassGroupData3_1_662796_2

set_option linter.all false

noncomputable section


noncomputable def E199RS1 : RelationCertificate Table 119 ![![199, 0, 0], ![12, 1, 0]]
  ![-106, -10, 1] ![![119, 0, 0], ![-43, -2, 1]] where
    su := ![![23681, 0, 0], ![1428, 119, 0]]
    hsu := by decide
    w := ![![-12614, -1190, 119], ![-1428, -119, 0]]
    hw := by decide
    g := ![![![6304, 430, -87], ![-2234, -1791, 0]], ![![408, 27, -6], ![-22, -105, 0]]]
    h := ![![![3750, -48798, -11261], ![52, 746980, 0]], ![![425, -5525, -1275], ![-1, 84575, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {119} * I199N1 =  Ideal.span {B.equivFun.symm ![-106, -10, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E199RS1 


noncomputable def E211RS1 : RelationCertificate Table 17 ![![211, 0, 0], ![41, 1, 0]]
  ![-391, -89, -14] ![![17, 0, 0], ![5, 1, 0]] where
    su := ![![3587, 0, 0], ![697, 17, 0]]
    hsu := by decide
    w := ![![-6647, -1513, -238], ![-8432, -1989, -323]]
    hw := by decide
    g := ![![![7753926, -45771576, -22897909], ![-411864, 129754800, 0]], ![![1530373, -9033864, -4519324], ![-81290, 25609500, 0]]]
    h := ![![![-11358, 476084, 34006], ![107, -2391760, 0]], ![![-14410, 603904, 43136], ![149, -3033905, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R211N1 : Ideal.span {17} * I211N1 =  Ideal.span {B.equivFun.symm ![-391, -89, -14]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E211RS1 


noncomputable def E227RS0 : RelationCertificate Table 49 ![![227, 0, 0], ![-107, 1, 0]]
  ![242, 47, -11] ![![49, 0, 0], ![-4, 1, 0]] where
    su := ![![11123, 0, 0], ![-5243, 49, 0]]
    hsu := by decide
    w := ![![11858, 2303, -539], ![-6174, -735, 196]]
    hw := by decide
    g := ![![![-3052, -9138, 9133], ![75, -149180, 0]], ![![1440, 4300, -4299], ![18, 70220, 0]]]
    h := ![![![6192, 646845, -18307], ![188, 1385226, 0]], ![![-3086, -337151, 9542], ![202, -722010, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N0 : Ideal.span {49} * I227N0 =  Ideal.span {B.equivFun.symm ![242, 47, -11]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E227RS0 


noncomputable def E227RS1 : RelationCertificate Table 49 ![![227, 0, 0], ![-78, 1, 0]]
  ![191, 13, -2] ![![49, 0, 0], ![-4, 1, 0]] where
    su := ![![11123, 0, 0], ![-3822, 49, 0]]
    hsu := by decide
    w := ![![9359, 637, -98], ![-1715, 0, 49]]
    hw := by decide
    g := ![![![-216501040596, -650669034573, 650579348971], ![4394594475, -10626129366522, 0]], ![![74710346415, 224533373317, -224502424541], ![-1516490015, 3666872934168, 0]]]
    h := ![![![3022, 229639, -8947], ![113, 676989, 0]], ![![-487, -42171, 1643], ![177, -124320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {49} * I227N1 =  Ideal.span {B.equivFun.symm ![191, 13, -2]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E227RS1 


noncomputable def E227RS2 : RelationCertificate Table 49 ![![227, 0, 0], ![-42, 1, 0]]
  ![1517, 358, 58] ![![49, 0, 0], ![-4, 1, 0]] where
    su := ![![11123, 0, 0], ![-2058, 49, 0]]
    hsu := by decide
    w := ![![74333, 17542, 2842], ![20776, 4851, 784]]
    hw := by decide
    g := ![![![-3883, -11644, 11644], ![88, -190190, 0]], ![![716, 2137, -2138], ![28, 34922, 0]]]
    h := ![![![1973445, 80973456, -5924884], ![-8232, 448316242, 0]], ![![551636, 22634116, -1656154], ![-2255, 125315658, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N2 : Ideal.span {49} * I227N2 =  Ideal.span {B.equivFun.symm ![1517, 358, 58]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E227RS2 


noncomputable def E229RS1 : RelationCertificate Table 7 ![![229, 0, 0], ![74, 1, 0]]
  ![-1024, -69, 23] ![![7, 0, 0], ![3, 1, 0]] where
    su := ![![1603, 0, 0], ![518, 7, 0]]
    hsu := by decide
    w := ![![-7168, -483, 161], ![7784, 448, -161]]
    hw := by decide
    g := ![![![1031099, -3906742, -2942567], ![-116205, 6866028, 0]], ![![336985, -1276708, -961622], ![-37959, 2243800, 0]]]
    h := ![![![5208, -391978, -15679], ![43, 1196838, 0]], ![![-5730, 425727, 17029], ![181, -1299888, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {7} * I229N1 =  Ideal.span {B.equivFun.symm ![-1024, -69, 23]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E229RS1 


noncomputable def E229RS2 : RelationCertificate Table 49 ![![229, 0, 0], ![-85, 1, 0]]
  ![306, 8, -5] ![![49, 0, 0], ![-4, 1, 0]] where
    su := ![![11221, 0, 0], ![-4165, 49, 0]]
    hsu := by decide
    w := ![![14994, 392, -245], ![-3577, -98, 49]]
    hw := by decide
    g := ![![![-7828659, -23528136, 23524892], ![158939, -384239902, 0]], ![![2917233, 8767398, -8766190], ![-59186, 143181103, 0]]]
    h := ![![![-1965040, -165302150, 5903647], ![7654, -450645056, 0]], ![![468872, 39434451, -1408373], ![-1577, 107505806, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N2 : Ideal.span {49} * I229N2 =  Ideal.span {B.equivFun.symm ![306, 8, -5]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E229RS2 
