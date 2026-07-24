import IdealArithmetic.Examples.NF3_1_469300_2.PrimesBelow3_1_469300_2F3
import IdealArithmetic.Examples.NF3_1_469300_2.ClassGroupData3_1_469300_2

set_option linter.all false

noncomputable section


noncomputable def E139RS1 : RelationCertificate Table 16 ![![139, 0, 0], ![61, 1, 0]]
  ![-56, -6, 1] ![![16, 0, 0], ![-63, -4, 1]] where
    su := ![![2224, 0, 0], ![976, 16, 0]]
    hsu := by decide
    w := ![![-896, -96, 16], ![-272, 32, 0]]
    hw := by decide
    g := ![![![12, 2, 0], ![-3, 0, 0]], ![![6, 1, 0], ![-1, 0, 0]]]
    h := ![![![-25896, -608, -3], ![59008, 418, 0]], ![![-7870, -190, -1], ![17933, 139, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {16} * I139N1 =  Ideal.span {B.equivFun.symm ![-56, -6, 1]} * (J0 ^ 8*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_0 E139RS1 


noncomputable def E149RS1 : RelationCertificate Table 24 ![![149, 0, 0], ![-64, 1, 0]]
  ![32, 10, 1] ![![24, 0, 0], ![-63, -4, 1]] where
    su := ![![3576, 0, 0], ![-1536, 24, 0]]
    hsu := by decide
    w := ![![768, 240, 24], ![264, 192, 24]]
    hw := by decide
    g := ![![![8462624, 1937834, 227099], ![-22527769, -4269346, 0]], ![![-3593394, -822847, -96432], ![9565824, 1812863, 0]]]
    h := ![![![288, -4, 0], ![670, 1, 0]], ![![95, -1, 0], ![221, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {24} * I149N1 =  Ideal.span {B.equivFun.symm ![32, 10, 1]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E149RS1 


noncomputable def E151RS1 : RelationCertificate Table 48 ![![151, 0, 0], ![43, 1, 0]]
  ![-16, 4, 1] ![![48, 0, 0], ![-63, -4, 1]] where
    su := ![![7248, 0, 0], ![2064, 48, 0]]
    hsu := by decide
    w := ![![-768, 192, 48], ![1008, 192, 0]]
    hw := by decide
    g := ![![![1198, 144, -2], ![-1541, -404, 0]], ![![371, 43, -1], ![-421, -116, 0]]]
    h := ![![![-16458, -469, -2], ![57794, 303, 0]], ![![21542, 544, 1], ![-75647, -151, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N1 : Ideal.span {48} * I151N1 =  Ideal.span {B.equivFun.symm ![-16, 4, 1]} * (J0 ^ 7*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7J1_1 E151RS1 


noncomputable def E151RS2 : RelationCertificate Table 144 ![![151, 0, 0], ![70, 1, 0]]
  ![212, 37, -5] ![![144, 0, 0], ![229, 68, -3]] where
    su := ![![21744, 0, 0], ![10080, 144, 0]]
    hsu := by decide
    w := ![![30528, 5328, -720], ![-122832, -14256, 2160]]
    hw := by decide
    g := ![![![-5086, 2363, 794], ![-6631, -1974, 0]], ![![-2479, 1173, 391], ![-3286, -973, 0]]]
    h := ![![![3112, 47, 0], ![-6710, -5, 0]], ![![-12913, -262, -1], ![27843, 166, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R151N2 : Ideal.span {144} * I151N2 =  Ideal.span {B.equivFun.symm ![212, 37, -5]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E151RS2 


noncomputable def E157RS0 : RelationCertificate Table 576 ![![157, 0, 0], ![23, 1, 0]]
  ![356, 37, -5] ![![576, 0, 0], ![7543, 708, -121]] where
    su := ![![90432, 0, 0], ![13248, 576, 0]]
    hsu := by decide
    w := ![![205056, 21312, -2880], ![-361152, -576, 2880]]
    hw := by decide
    g := ![![![-1464, 90, 5], ![-2083, -360, 0]], ![![-3854, -327, 59], ![-41, -55, 0]]]
    h := ![![![1958, 86, 0], ![-13350, -5, 0]], ![![-3506, -176, -1], ![23905, 162, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N0 : Ideal.span {576} * I157N0 =  Ideal.span {B.equivFun.symm ![356, 37, -5]} * (J0 ^ 9*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_9J1_2 E157RS0 


noncomputable def E157RS1 : RelationCertificate Table 192 ![![157, 0, 0], ![-15, 1, 0]]
  ![188, 7, -2] ![![192, 0, 0], ![-15, -4, 1]] where
    su := ![![30144, 0, 0], ![-2880, 192, 0]]
    hsu := by decide
    w := ![![36096, 1344, -384], ![2880, -192, 0]]
    hw := by decide
    g := ![![![61173899, 12856566, -621786], ![-5050129, -31108264, 0]], ![![-5334925, -1121210, 54225], ![440519, 2712930, 0]]]
    h := ![![![464, -31, 0], ![4844, -2, 0]], ![![60, -4, 0], ![627, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N1 : Ideal.span {192} * I157N1 =  Ideal.span {B.equivFun.symm ![188, 7, -2]} * (J0 ^ 11*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_11J1_1 E157RS1 


noncomputable def E157RS2 : RelationCertificate Table 4 ![![157, 0, 0], ![-8, 1, 0]]
  ![-8, 1, 0] ![![4, 0, 0], ![-63, -4, 1]] where
    su := ![![628, 0, 0], ![-32, 4, 0]]
    hsu := by decide
    w := ![![-32, 4, 0], ![884, 64, -12]]
    hw := by decide
    g := ![![![8, 3, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-24, 11, -1], ![-470, 157, 0]], ![![713, -89, 0], ![13965, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R157N2 : Ideal.span {4} * I157N2 =  Ideal.span {B.equivFun.symm ![-8, 1, 0]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E157RS2 


noncomputable def E179RS1 : RelationCertificate Table 288 ![![179, 0, 0], ![80, 1, 0]]
  ![-332, -115, -10] ![![288, 0, 0], ![-111, -4, 1]] where
    su := ![![51552, 0, 0], ![23040, 288, 0]]
    hsu := by decide
    w := ![![-95616, -33120, -2880], ![8352, 3168, 288]]
    hw := by decide
    g := ![![![3642, -189, -39], ![-1213, -3100, 0]], ![![1687, -84, -18], ![-444, -1402, 0]]]
    h := ![![![-5668, -147, -1], ![12678, 169, 0]], ![![351, 4, 0], ![-785, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R179N1 : Ideal.span {288} * I179N1 =  Ideal.span {B.equivFun.symm ![-332, -115, -10]} * (J0 ^ 8*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8J1_2 E179RS1 


noncomputable def E193RS1 : RelationCertificate Table 72 ![![193, 0, 0], ![32, 1, 0]]
  ![28, -7, -1] ![![72, 0, 0], ![-1295, -160, 21]] where
    su := ![![13896, 0, 0], ![2304, 72, 0]]
    hsu := by decide
    w := ![![2016, -504, -72], ![-31320, -2160, 1008]]
    hw := by decide
    g := ![![![1337564821, -6382427486, -722255559], ![-10085068331, -1648680220, 0]], ![![218308104, -1041691412, -117881102], ![-1646008496, -269085111, 0]]]
    h := ![![![44252, 1415, 1], ![-266894, -194, 0]], ![![-688691, -22388, -27], ![4153654, 5225, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R193N1 : Ideal.span {72} * I193N1 =  Ideal.span {B.equivFun.symm ![28, -7, -1]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E193RS1 
