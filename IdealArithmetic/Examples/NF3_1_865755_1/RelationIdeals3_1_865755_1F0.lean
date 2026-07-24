import IdealArithmetic.Examples.NF3_1_865755_1.PrimesBelow3_1_865755_1F0
import IdealArithmetic.Examples.NF3_1_865755_1.ClassGroupData3_1_865755_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 256 ![![2, 0, 0], ![-25, 0, 1]]
  ![-107, -16, -3] ![![256, 0, 0], ![-111, 1, 0]] where
    su := ![![512, 0, 0], ![-6400, 0, 256]]
    hsu := by decide
    w := ![![-27392, -4096, -768], ![11008, 1536, 256]]
    hw := by decide
    g := ![![![69519, -5008194, 227654], ![-49684, -11655885, 0]], ![![-869268, 62630560, -2846954], ![621580, 145764045, 0]]]
    h := ![![![9, -8, -4], ![5, 0, 0]], ![![9, 3, 1], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {256} * I2N0 =  Ideal.span {B.equivFun.symm ![-107, -16, -3]} * (J0 ^ 8) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_8 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 8 ![![3, 0, 0], ![1, 1, 0]]
  ![50989, 10624, 2989] ![![8, 0, 0], ![1, 1, 0]] where
    su := ![![24, 0, 0], ![8, 8, 0]]
    hsu := by decide
    w := ![![407912, 84992, 23912], ![906168, 188808, 53120]]
    hw := by decide
    g := ![![![177, 0, 2], ![24, -9, 0]], ![![-272, 18, 5], ![-31, -6, 0]]]
    h := ![![![16759, 3304, 5978], ![6690, -2989, 0]], ![![37231, 7341, 13280], ![14858, -6640, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {8} * I3N0 =  Ideal.span {B.equivFun.symm ![50989, 10624, 2989]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 2 ![![5, 0, 0], ![-28, -1, 1]]
  ![19, 2, -1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![10, 0, 0], ![-56, -2, 2]]
    hsu := by decide
    w := ![![38, 4, -2], ![-256, -16, 10]]
    hw := by decide
    g := ![![![13, 0, 1], ![7, 0, 0]], ![![19, -2, -6], ![9, 3, 0]]]
    h := ![![![83, 4, 25], ![-342, -36, 0]], ![![-420, -21, -178], ![2383, 248, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2} * I5N0 =  Ideal.span {B.equivFun.symm ![19, 2, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 128 ![![5, 0, 0], ![-2, 1, 0]]
  ![-229527, -47824, -13455] ![![128, 0, 0], ![17, 1, 0]] where
    su := ![![640, 0, 0], ![-256, 128, 0]]
    hsu := by decide
    w := ![![-29379456, -6121472, -1722240], ![-7751552, -1615104, -454400]]
    hw := by decide
    g := ![![![-1237, -11519, -3200], ![-193, 81918, 0]], ![![-726460391921, -6715014613109, -1865605066300], ![-148944072360, 47759489697261, 0]]]
    h := ![![![-20141343, -4642757, 244047], ![7127991, 0, 411230]], ![![-5314145, -1224957, 64390], ![1880667, 0, 108500]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {128} * I5N1 =  Ideal.span {B.equivFun.symm ![-229527, -47824, -13455]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 64 ![![7, 0, 0], ![-23, 2, 1]]
  ![411, 16, -13] ![![64, 0, 0], ![17, 1, 0]] where
    su := ![![448, 0, 0], ![-1472, 128, 64]]
    hsu := by decide
    w := ![![26304, 1024, -832], ![3392, 192, -128]]
    hw := by decide
    g := ![![![-57193, -571948, -158979], ![-24090, 2034931, 0]], ![![201335, 2013898, 559785], ![84994, -7165250, 0]]]
    h := ![![![16, 6, 0], ![-13, 0, 0]], ![![1, 1, 0], ![-2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {64} * I7N0 =  Ideal.span {B.equivFun.symm ![411, 16, -13]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 8 ![![7, 0, 0], ![-2, 1, 0]]
  ![153, 32, 9] ![![8, 0, 0], ![1, 1, 0]] where
    su := ![![56, 0, 0], ![-16, 8, 0]]
    hsu := by decide
    w := ![![1224, 256, 72], ![2728, 568, 160]]
    hw := by decide
    g := ![![![92, 103, 267], ![32, -427, 0]], ![![-7, -16, -38], ![-1, 61, 0]]]
    h := ![![![15, 8, -18], ![3, 27, 0]], ![![31, 19, -40], ![-2, 60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {8} * I7N1 =  Ideal.span {B.equivFun.symm ![153, 32, 9]} * (J0 ^ 3) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 64 ![![11, 0, 0], ![0, 1, 0]]
  ![-637439, -132816, -37367] ![![64, 0, 0], ![17, 1, 0]] where
    su := ![![704, 0, 0], ![0, 64, 0]]
    hsu := by decide
    w := ![![-40796096, -8500224, -2391488], ![-21527488, -4485440, -1261952]]
    hw := by decide
    g := ![![![-328, -2409, -662], ![-90, 8535, 0]], ![![94, -165, -53], ![25, 615, 0]]]
    h := ![![![80954753, 40162356, 202528358], ![3651129, -445569861, 0]], ![![42718609, 21193073, 106871177], ![1926645, -235120533, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {64} * I11N0 =  Ideal.span {B.equivFun.symm ![-637439, -132816, -37367]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E11RS0 


noncomputable def E13RS0 : RelationCertificate Table 32 ![![13, 0, 0], ![-29, -4, 1]]
  ![-11789, 2672, -629] ![![32, 0, 0], ![-15, 1, 0]] where
    su := ![![416, 0, 0], ![-928, -128, 32]]
    hsu := by decide
    w := ![![-377248, 85504, -20128], ![6688, -73728, 23424]]
    hw := by decide
    g := ![![![95079954613845, -902019395677127, 322961802413622], ![-72756834840135, -2066955535454976, 0]], ![![-211949065474096, 2010751569534917, -719935684545491], ![162187110988962, 4607588381117276, 0]]]
    h := ![![![-164, 308, -74], ![333, 0, 0]], ![![25, -176, 56], ![4, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {32} * I13N0 =  Ideal.span {B.equivFun.symm ![-11789, 2672, -629]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 16 ![![13, 0, 0], ![-5, 1, 0]]
  ![-11071675, -2306880, -649027] ![![16, 0, 0], ![1, 1, 0]] where
    su := ![![208, 0, 0], ![-80, 16, 0]]
    hsu := by decide
    w := ![![-177146800, -36910080, -10384432], ![-196763968, -40997488, -11534400]]
    hw := by decide
    g := ![![![-7656, -10127, -26054], ![-1105, 83025, 0]], ![![-2900, 247, 1158], ![-158, -3321, 0]]]
    h := ![![![-1386992010, 3318125545, -4223765104], ![788698895, 10981659465, 0]], ![![-1540586967, 3685573482, -4691503215], ![876039107, 12197764179, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {16} * I13N1 =  Ideal.span {B.equivFun.symm ![-11071675, -2306880, -649027]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 128 ![![17, 0, 0], ![6, 1, 0]]
  ![-1045351, -217808, -61279] ![![128, 0, 0], ![17, 1, 0]] where
    su := ![![2176, 0, 0], ![768, 128, 0]]
    hsu := by decide
    w := ![![-133804928, -27879424, -7843712], ![-35303424, -7355776, -2069504]]
    hw := by decide
    g := ![![![-724, -5211, -1442], ![-25, 37025, 0]], ![![-209, -1963, -545], ![63, 13950, 0]]]
    h := ![![![-337761, -1203267, -861912], ![-189984, 2918245, 0]], ![![-89116, -317473, -227409], ![-50125, 769957, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {128} * I17N0 =  Ideal.span {B.equivFun.symm ![-1045351, -217808, -61279]} * (J0 ^ 7) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_7 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 64 ![![17, 0, 0], ![-4, 1, 0]]
  ![14974713, 3120112, 877825] ![![64, 0, 0], ![17, 1, 0]] where
    su := ![![1088, 0, 0], ![-256, 64, 0]]
    hsu := by decide
    w := ![![958381632, 199687168, 56180800], ![505723520, 105371904, 29645760]]
    hw := by decide
    g := ![![![385, 578, 120], ![155, -1860, 0]], ![![455825173, 4559180936, 1267273890], ![192315776, -16221105481, 0]]]
    h := ![![![-6725729859, 10741385173, -18119046275], ![2214370871, 61604932900, 0]], ![![-3549066118, 5668066810, -9561147205], ![1168490086, 32507993140, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {64} * I17N1 =  Ideal.span {B.equivFun.symm ![14974713, 3120112, 877825]} * (J0 ^ 6) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_6 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 32 ![![17, 0, 0], ![-2, 1, 0]]
  ![25571, 5328, 1499] ![![32, 0, 0], ![-15, 1, 0]] where
    su := ![![544, 0, 0], ![-64, 32, 0]]
    hsu := by decide
    w := ![![818272, 170496, 47968], ![45312, 9440, 2656]]
    hw := by decide
    g := ![![![4060, -38840, 13907], ![-3092, -89001, 0]], ![![-502, 4909, -1758], ![395, 11253, 0]]]
    h := ![![![273, 929, -2998], ![28, 10493, 0]], ![![16, 51, -166], ![9, 581, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {32} * I17N2 =  Ideal.span {B.equivFun.symm ![25571, 5328, 1499]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E17RS2 


noncomputable def E19RS1 : RelationCertificate Table 16 ![![19, 0, 0], ![5, 1, 0]]
  ![-55, 0, 1] ![![16, 0, 0], ![1, 1, 0]] where
    su := ![![304, 0, 0], ![80, 16, 0]]
    hsu := by decide
    w := ![![-880, 0, 16], ![224, -16, 0]]
    hw := by decide
    g := ![![![63, 64, 164], ![23, -525, 0]], ![![24, 25, 64], ![6, -205, 0]]]
    h := ![![![6120, 20353, 17079], ![2693, -64900, 0]], ![![-1589, -5274, -4425], ![-685, 16815, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {16} * I19N1 =  Ideal.span {B.equivFun.symm ![-55, 0, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 4 ![![23, 0, 0], ![-6, 1, 0]]
  ![21, 4, 1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![92, 0, 0], ![-24, 4, 0]]
    hsu := by decide
    w := ![![84, 16, 4], ![308, 68, 20]]
    hw := by decide
    g := ![![![2, 19, 57], ![9, -45, 0]], ![![8, -5, -13], ![3, 10, 0]]]
    h := ![![![253, -683, 687], ![-87, -3160, 0]], ![![919, -2499, 2515], ![-346, -11568, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {4} * I23N1 =  Ideal.span {B.equivFun.symm ![21, 4, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 2 ![![29, 0, 0], ![-5, 1, 0]]
  ![461, 96, 27] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![58, 0, 0], ![-10, 2, 0]]
    hsu := by decide
    w := ![![922, 192, 54], ![8186, 1706, 480]]
    hw := by decide
    g := ![![![816, 839, 3167], ![828, -1265, 0]], ![![39, -3, -3], ![19, 0, 0]]]
    h := ![![![7665, -15874, 19928], ![-1866, -115577, 0]], ![![68050, -140936, 176930], ![-16587, -1026146, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2} * I29N1 =  Ideal.span {B.equivFun.symm ![461, 96, 27]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 16 ![![31, 0, 0], ![-15, 1, 0]]
  ![-23, 0, 1] ![![16, 0, 0], ![1, 1, 0]] where
    su := ![![496, 0, 0], ![-240, 16, 0]]
    hsu := by decide
    w := ![![-368, 0, 16], ![256, 16, 0]]
    hw := by decide
    g := ![![![215, 214, 539], ![29, -1725, 0]], ![![-97, -96, -239], ![4, 765, 0]]]
    h := ![![![1050, -10029, 3591], ![-797, -22264, 0]], ![![-697, 6758, -2420], ![559, 15004, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {16} * I31N1 =  Ideal.span {B.equivFun.symm ![-23, 0, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E31RS1 
