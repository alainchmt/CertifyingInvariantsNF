import IdealArithmetic.Examples.NF3_1_428868_2.PrimesBelow3_1_428868_2F0
import IdealArithmetic.Examples.NF3_1_428868_2.ClassGroupData3_1_428868_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![0, 1, 0]]
  ![33, 2, 1] ![![2, 0, 0], ![20, 1, 1]] where
    su := ![![4, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![66, 4, 2], ![850, 50, 26]]
    hw := by decide
    g := ![![![4, -45, -13], ![33, -7, 0]], ![![-10, 0, -1], ![1, 0, 0]]]
    h := ![![![4719, -1148, -49], ![-573, 0, -99]], ![![60775, -14780, -631], ![-7390, 0, -1275]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![33, 2, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![20, 1, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![20, 1, 1]] where
    su := ![![2, 0, 0], ![20, 1, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![20, 1, 1]]
    hw := by decide
    g := ![![![-4, -13, -4], ![10, -2, 0]], ![![10, -127, -37], ![95, -20, 0]]]
    h := ![![![-4, -13, -4], ![10, -2, 0]], ![![10, -127, -37], ![95, -20, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 5 ![![3, 0, 0], ![-1, 1, 0]]
  ![218968, 13064, 6693] ![![5, 0, 0], ![0, 1, 0]] where
    su := ![![15, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![1094840, 65320, 33465], ![635835, 37935, 19435]]
    hw := by decide
    g := ![![![-14, 22, 23], ![5, -69, 0]], ![![-141, 33, 0], ![11, 23, 0]]]
    h := ![![![66750, 10594, -60237], ![-18718, 93702, 0]], ![![38766, 6152, -34983], ![-10869, 54418, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {5} * I3N0 =  Ideal.span {B.equivFun.symm ![218968, 13064, 6693]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![0, 1, 0]] where
    su := ![![5, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 25 ![![5, 0, 0], ![21, 3, 1]]
  ![-66642, -3976, -2037] ![![25, 0, 0], ![5, 1, 0]] where
    su := ![![125, 0, 0], ![525, 75, 25]]
    hsu := by decide
    w := ![![-1666050, -99400, -50925], ![-526725, -31425, -16100]]
    hw := by decide
    g := ![![![1788107881, -232454024463, -77603882013], ![-8940539393, 970048525159, 0]], ![![7152431524, -929816100085, -310415528798], ![-35762157676, 3880194109981, 0]]]
    h := ![![![-867, 985, 186], ![-2967, 0, 0]], ![![-291, 309, 58], ![-934, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {25} * I5N1 =  Ideal.span {B.equivFun.symm ![-66642, -3976, -2037]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS1 


noncomputable def E11RS0 : RelationCertificate Table 50 ![![11, 0, 0], ![-5, 1, 0]]
  ![580741, 34648, 17751] ![![50, 0, 0], ![40, 1, 1]] where
    su := ![![550, 0, 0], ![-250, 50, 0]]
    hsu := by decide
    w := ![![29037050, 1732400, 887550], ![26521200, 1582300, 810650]]
    hw := by decide
    g := ![![![895, 180, 2], ![759, -798, 0]], ![![13511711666, 2587090852, 16464496], ![10861440481, -11684665281, 0]]]
    h := ![![![85736, 1225835, -613023], ![72471, 3380502, 0]], ![![78309, 1119625, -559909], ![66195, 3087606, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {50} * I11N0 =  Ideal.span {B.equivFun.symm ![580741, 34648, 17751]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 50 ![![11, 0, 0], ![-1, 1, 0]]
  ![-9, -2, 1] ![![50, 0, 0], ![40, 1, 1]] where
    su := ![![550, 0, 0], ![-50, 50, 0]]
    hsu := by decide
    w := ![![-450, -100, 50], ![-550, 0, 0]]
    hw := by decide
    g := ![![![4545, 874, 5], ![3699, -3950, 0]], ![![-435, -80, -1], ![-309, 359, 0]]]
    h := ![![![0, -1, -1], ![9, 6, 0]], ![![0, -1, 0], ![11, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {50} * I11N1 =  Ideal.span {B.equivFun.symm ![-9, -2, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 5 ![![13, 0, 0], ![24, 6, 1]]
  ![-237, 74, 8] ![![5, 0, 0], ![0, 1, 0]] where
    su := ![![65, 0, 0], ![120, 30, 5]]
    hsu := by decide
    w := ![![-1185, 370, 40], ![760, -395, 140]]
    hw := by decide
    g := ![![![-1361, 1350, 2930], ![273, -7429, 0]], ![![-4626, 2343, 5285], ![471, -13566, 0]]]
    h := ![![![-9, 8, 1], ![-5, 0, 0]], ![![-16, -13, 1], ![15, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {5} * I13N0 =  Ideal.span {B.equivFun.symm ![-237, 74, 8]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 25 ![![13, 0, 0], ![2, 1, 0]]
  ![256, -32, -59] ![![25, 0, 0], ![5, 1, 0]] where
    su := ![![325, 0, 0], ![50, 25, 0]]
    hsu := by decide
    w := ![![6400, -800, -1475], ![-4325, 1775, -300]]
    hw := by decide
    g := ![![![442, -805718, -269065], ![-32132, 3361026, 0]], ![![-1379, -103375, -34541], ![-4392, 430900, 0]]]
    h := ![![![9476, 5034, 201], ![-61466, -1336, 0]], ![![-6323, -3361, -142], ![41013, 917, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {25} * I13N1 =  Ideal.span {B.equivFun.symm ![256, -32, -59]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 5 ![![17, 0, 0], ![6, 1, 0]]
  ![23, -6, -2] ![![5, 0, 0], ![0, 1, 0]] where
    su := ![![85, 0, 0], ![30, 5, 0]]
    hsu := by decide
    w := ![![115, -30, -10], ![-190, 75, -10]]
    hw := by decide
    g := ![![![275, 16, 10], ![6, -4, 0]], ![![144, 9, 6], ![2, -4, 0]]]
    h := ![![![13, 2, 0], ![-33, -1, 0]], ![![-34, -11, -2], ![90, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {5} * I17N0 =  Ideal.span {B.equivFun.symm ![23, -6, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 50 ![![17, 0, 0], ![-4, 1, 0]]
  ![54, -13, -6] ![![50, 0, 0], ![5, 1, 0]] where
    su := ![![850, 0, 0], ![-200, 50, 0]]
    hsu := by decide
    w := ![![2700, -650, -300], ![-300, 150, -50]]
    hw := by decide
    g := ![![![-42, -128, -43], ![15, 1044, 0]], ![![-2, 23, 8], ![46, -198, 0]]]
    h := ![![![10, 240, -162], ![29, 1374, 0]], ![![2, -29, 19], ![10, -162, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {50} * I17N1 =  Ideal.span {B.equivFun.symm ![54, -13, -6]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 2 ![![17, 0, 0], ![-2, 1, 0]]
  ![-3, 2, -1] ![![2, 0, 0], ![20, 1, 1]] where
    su := ![![34, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-6, 4, -2], ![130, -52, 8]]
    hw := by decide
    g := ![![![1, 3, -6], ![31, 0, 0]], ![![-6, 19, 5], ![-12, 3, 0]]]
    h := ![![![1, -2, 3], ![10, -26, 0]], ![![5, 30, -64], ![10, 546, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {2} * I17N2 =  Ideal.span {B.equivFun.symm ![-3, 2, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS2 


noncomputable def E19RS0 : RelationCertificate Table 50 ![![19, 0, 0], ![0, 1, 0]]
  ![38703, 2309, 1183] ![![50, 0, 0], ![5, 1, 0]] where
    su := ![![950, 0, 0], ![0, 50, 0]]
    hsu := by decide
    w := ![![1935150, 115450, 59150], ![305900, 18250, 9350]]
    hw := by decide
    g := ![![![-10, 15, 4], ![43, -112, 0]], ![![-6, 20, 7], ![36, -168, 0]]]
    h := ![![![2037, -58307, -117117], ![-3061, 1113203, 0]], ![![322, -9217, -18513], ![-479, 175967, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {50} * I19N0 =  Ideal.span {B.equivFun.symm ![38703, 2309, 1183]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E19RS0 


noncomputable def E23RS0 : RelationCertificate Table 10 ![![23, 0, 0], ![-10, 1, 0]]
  ![-107, 34, 3] ![![10, 0, 0], ![20, 1, 1]] where
    su := ![![230, 0, 0], ![-100, 10, 0]]
    hsu := by decide
    w := ![![-1070, 340, 30], ![1090, -280, -100]]
    hw := by decide
    g := ![![![-35498, 21459, 5039], ![-68337, 18216, 0]], ![![15637, -9445, -2220], ![30136, -8019, 0]]]
    h := ![![![-5199, 526, -1], ![-11947, 13, 0]], ![![5293, -532, 0], ![12163, -5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {10} * I23N0 =  Ideal.span {B.equivFun.symm ![-107, 34, 3]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 25 ![![23, 0, 0], ![-7, 1, 0]]
  ![16, -2, 1] ![![25, 0, 0], ![5, 1, 0]] where
    su := ![![575, 0, 0], ![-175, 25, 0]]
    hsu := by decide
    w := ![![400, -50, 25], ![175, -25, 0]]
    hw := by decide
    g := ![![![-7634, 992004, 331177], ![38176, -4139712, 0]], ![![1985, -258335, -86244], ![-9926, 1078050, 0]]]
    h := ![![![64, -6, -1], ![208, 12, 0]], ![![35, -5, 0], ![114, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {25} * I23N1 =  Ideal.span {B.equivFun.symm ![16, -2, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 2 ![![23, 0, 0], ![-6, 1, 0]]
  ![-17, 3, 3] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![46, 0, 0], ![-12, 2, 0]]
    hsu := by decide
    w := ![![-34, 6, 6], ![268, -98, 6]]
    hw := by decide
    g := ![![![4202, -597, 156], ![1803, 0, 0]], ![![-566, 80, -21], ![-242, 0, 0]]]
    h := ![![![-67, 14, -1], ![-254, 13, 0]], ![![598, -98, -1], ![2270, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {2} * I23N2 =  Ideal.span {B.equivFun.symm ![-17, 3, 3]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E23RS2 
