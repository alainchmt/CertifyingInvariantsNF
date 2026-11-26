import IdealArithmetic.Examples.NF4_0_76176_2.PrimesBelow4_0_76176_2F0
import IdealArithmetic.Examples.NF4_0_76176_2.ClassGroupData4_0_76176_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 8 ![![2, 0, 0, 0], ![-1, 1, 0, -1]]
  ![2, -2, -2, 5] ![![8, 0, 0, 0], ![-6, 0, -5, 6]] where
    su := ![![16, 0, 0, 0], ![-8, 8, 0, -8]]
    hsu := by decide
    w := ![![16, -16, -16, 40], ![56, 24, 16, -32]]
    hw := by decide
    g := ![![![286825, -109367, -118431, 291094], ![77238, 41655, 15, 0]], ![![288228, -109902, -119011, 292519], ![77615, 41859, 15, 0]]]
    h := ![![![-36374, 35483, -280, -35198], ![-71292, 27, 45, 0]], ![![133822, -130551, 1015, 129522], ![262279, -97, -165, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {8} * I2N0 =  Ideal.span {B.equivFun.symm ![2, -2, -2, 5]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0, 0], ![0, -1, 0, 0]]
  ![1, 0, 0, 0] ![![2, 0, 0, 0], ![0, 0, -1, 1]] where
    su := ![![2, 0, 0, 0], ![0, -1, 0, 0]]
    hsu := by decide
    w := ![![2, 0, 0, 0], ![0, 0, -1, 1]]
    hw := by decide
    g := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![-8, -7, -34, 44], ![-45, 1, 1, 0]]]
    h := ![![![1, 0, 0, 0], ![0, 0, 0, 0]], ![![8, -12, -6, 18], ![-9, 5, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 6 ![![3, 0, 0, 0], ![-3, 1, 1, -3]]
  ![-1, 0, -1, 1] ![![6, 0, 0, 0], ![-4, 1, 0, -3]] where
    su := ![![18, 0, 0, 0], ![-18, 6, 6, -18]]
    hsu := by decide
    w := ![![-6, 0, -6, 6], ![-36, -12, -18, 36]]
    hw := by decide
    g := ![![![2935, -30008, -47161, 78695], ![-46305, 11302, 8, 0]], ![![-2505, 25652, 40315, -67271], ![39583, -9661, -7, 0]]]
    h := ![![![-1075, -587, -1114, 1931], ![-1416, 527, 1, 0]], ![![-1250, -681, -1293, 2241], ![-1646, 612, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {6} * I3N0 =  Ideal.span {B.equivFun.symm ![-1, 0, -1, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 8 ![![3, 0, 0, 0], ![-1, 0, 0, -1]]
  ![-1, 0, -1, 2] ![![24, 0, 0, 0], ![10, -10, 7, -8]] where
    su := ![![24, 0, 0, 0], ![-8, 0, 0, -8]]
    hsu := by decide
    w := ![![-24, 0, -24, 48], ![72, -16, -48, 80]]
    hw := by decide
    g := ![![![-6149270313, 3119151672, 5134789419, -9055858154], ![654423822, 2203722630, -3, 0]], ![![2049757291, -1039717483, -1711596923, 3018620174], ![-218141306, -734574400, 1, 0]]]
    h := ![![![-35847, 67068, 76704, -151580], ![62478, -28566, -69, 0]], ![![-23836, 44604, 51012, -100809], ![41551, -18998, -46, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {8} * I3N1 =  Ideal.span {B.equivFun.symm ![-1, 0, -1, 2]} * (J0 ^ 5*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 6 ![![5, 0, 0, 0], ![-2, -1, 0, 0]]
  ![2, 0, 2, -5] ![![6, 0, 0, 0], ![-10, 4, 3, -9]] where
    su := ![![30, 0, 0, 0], ![-12, -6, 0, 0]]
    hsu := by decide
    w := ![![12, 0, 12, -30], ![-78, -42, -54, 90]]
    hw := by decide
    g := ![![![195669915, 38376866, 160515531, -251639900], ![157185685, -51962431, 811913, 0]], ![![-39082497, -7665276, -32060872, 50261770], ![-31395778, 10378814, -162169, 0]]]
    h := ![![![14, 10, 2, -1], ![34, 8, 0, 0]], ![![-97, -57, -6, 3], ![-236, -21, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {6} * I5N0 =  Ideal.span {B.equivFun.symm ![2, 0, 2, -5]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 6 ![![5, 0, 0, 0], ![-4, 1, 2, -4]]
  ![-4, 0, -4, 7] ![![6, 0, 0, 0], ![-10, 4, 3, -9]] where
    su := ![![30, 0, 0, 0], ![-24, 6, 12, -24]]
    hsu := by decide
    w := ![![-24, 0, -24, 42], ![-6, 18, 42, -60]]
    hw := by decide
    g := ![![![24712283932585, -4475452995665, 89778507454887, -139971684268117], ![110440078957455, -41371243976871, 55, 13109252261333]], ![![-24707535760090, 4474593090410, -89761257662412, 139944790504804], ![-110418859295380, 41363295020116, -55, -13106733486421]]]
    h := ![![![116, 94, 8, -61], ![-22, 0, 0, -112]], ![![119, 94, 9, -62], ![-19, 0, 0, -112]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {6} * I5N1 =  Ideal.span {B.equivFun.symm ![-4, 0, -4, 7]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E13RS0 : RelationCertificate Table 12 ![![13, 0, 0, 0], ![1, 1, 0, -1]]
  ![-10, 6, 2, -5] ![![12, 0, 0, 0], ![-6, 4, -3, 4]] where
    su := ![![156, 0, 0, 0], ![12, 12, 0, -12]]
    hsu := by decide
    w := ![![-120, 72, 24, -60], ![-60, 12, 132, -216]]
    hw := by decide
    g := ![![![40635928146, -12093472181, -32836687755, 54209182660], ![1929778039, 20136581195, 59225239, 0]], ![![1281632, -381421, -1035647, 1709721], ![60867, 635095, 1868, 0]]]
    h := ![![![21072, -29636, -29938, 59625], ![-5242, 43464, -220, 0]], ![![-4817, 6775, 6845, -13632], ![1200, -9936, 50, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {12} * I13N0 =  Ideal.span {B.equivFun.symm ![-10, 6, 2, -5]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 24 ![![13, 0, 0, 0], ![4, 1, 0, -1]]
  ![2, -6, -10, 19] ![![24, 0, 0, 0], ![28, -19, -8, 25]] where
    su := ![![312, 0, 0, 0], ![96, 24, 0, -24]]
    hsu := by decide
    w := ![![48, -144, -240, 456], ![408, -72, -24, -24]]
    hw := by decide
    g := ![![![9004803840199, 17980085762, 11431512598757, -16815892274933], ![-10835688406919, 3967493379525, 1997983, 0]], ![![2079311942282, 4151806951, 2639666680926, -3882981378433], ![-2502084077262, 916139486374, 461357, 0]]]
    h := ![![![-257107514, 502075007, 377561858, -753783670], ![17494519, -545373700, 4928, 0]], ![![321414421, -627652408, -471996427, 942317640], ![-21870179, 681780830, -6160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {24} * I13N1 =  Ideal.span {B.equivFun.symm ![2, -6, -10, 19]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 12 ![![13, 0, 0, 0], ![-5, 1, 0, -1]]
  ![-4, 6, 8, -17] ![![12, 0, 0, 0], ![-6, 4, -3, 4]] where
    su := ![![156, 0, 0, 0], ![-60, 12, 0, -12]]
    hsu := by decide
    w := ![![-48, 72, 96, -204], ![108, -12, 12, -12]]
    hw := by decide
    g := ![![![-14038482031, 4249246158, 11215961578, -18600868428], ![-568623463, -6756987185, 23625829, 0]], ![![6477847891, -1960751186, -5175437970, 8583092950], ![262382817, 3117910829, -10901786, 0]]]
    h := ![![![27139541, -15819297, -51967114, 102430942], ![-19534455, 75064528, -2754, 0]], ![![4526063, -2638184, -8666552, 17082402], ![-3257750, 12518506, -459, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {12} * I13N2 =  Ideal.span {B.equivFun.symm ![-4, 6, 8, -17]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS2 


noncomputable def E13RS3 : RelationCertificate Table 24 ![![13, 0, 0, 0], ![-8, 1, 0, -1]]
  ![8, -6, -4, 7] ![![24, 0, 0, 0], ![28, -19, -8, 25]] where
    su := ![![312, 0, 0, 0], ![-192, 24, 0, -24]]
    hsu := by decide
    w := ![![192, -144, -96, 168], ![408, 24, 264, -432]]
    hw := by decide
    g := ![![![-4431813255004863340, -8844991212692674, -5626157151489754475, 8276143541021512922], ![5332922059598368631, -1952649979253070325, 11628565, 0]], ![![3068124283985639700, 6123347435873020, 3894963164910306423, -5729536764051025387], ![-3691957836260073312, 1351810754368942010, -8050403, 0]]]
    h := ![![![300502912, 22488596, -720535708, 1418577365], ![-292316300, 1040773800, -11818, 0]], ![![593097561, 44385368, -1422109273, 2799822413], ![-576939808, 2054157840, -23325, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N3 : Ideal.span {24} * I13N3 =  Ideal.span {B.equivFun.symm ![8, -6, -4, 7]} * (J0 ^ 4*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_1 E13RS3 


noncomputable def E23RS0 : RelationCertificate Table 12 ![![23, 0, 0, 0], ![6, 1, 0, -1]]
  ![-5, 0, -5, 8] ![![12, 0, 0, 0], ![10, -4, -5, 10]] where
    su := ![![276, 0, 0, 0], ![72, 12, 0, -12]]
    hsu := by decide
    w := ![![-60, 0, -60, 96], ![-72, 36, -24, 24]]
    hw := by decide
    g := ![![![15225287, -3253848, 5623632, -8410893], ![4420123, 11345331, -57, 0]], ![![4533332, -968834, 1674437, -2504344], ![1316092, 3378074, -17, 0]]]
    h := ![![![-2206735, 5117750, 3277670, -6574684], ![-67285, -8407185, 19875, 0]], ![![-1088670, 2524788, 1617004, -3243551], ![-33192, -4147596, 9805, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {12} * I23N0 =  Ideal.span {B.equivFun.symm ![-5, 0, -5, 8]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 12 ![![23, 0, 0, 0], ![-10, 1, 0, -1]]
  ![-1, 0, -1, 4] ![![12, 0, 0, 0], ![10, -4, -5, 10]] where
    su := ![![276, 0, 0, 0], ![-120, 12, 0, -12]]
    hsu := by decide
    w := ![![-12, 0, -12, 48], ![-72, 12, 24, -48]]
    hw := by decide
    g := ![![![761754755, -162844116, 281437679, -420928256], ![221037760, 567656089, -49620, 0]], ![![-330092204, 70565459, -121955760, 182401394], ![-95782579, -245983166, 21502, 0]]]
    h := ![![![-50023, -22104, 93795, -186312], ![28898, -239690, 38, 0]], ![![-279112, -123323, 523311, -1039494], ![161188, -1337303, 212, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {12} * I23N1 =  Ideal.span {B.equivFun.symm ![-1, 0, -1, 4]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E23RS1 
