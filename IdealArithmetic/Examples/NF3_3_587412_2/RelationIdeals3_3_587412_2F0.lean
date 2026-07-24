import IdealArithmetic.Examples.NF3_3_587412_2.PrimesBelow3_3_587412_2F0
import IdealArithmetic.Examples.NF3_3_587412_2.ClassGroupData3_3_587412_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 65 ![![2, 0, 0], ![0, 1, 0]]
  ![272, 19, -2] ![![65, 0, 0], ![-23, 1, 0]] where
    su := ![![130, 0, 0], ![0, 65, 0]]
    hsu := by decide
    w := ![![17680, 1235, -130], ![-8580, -585, 65]]
    hw := by decide
    g := ![![![-17028651, -3519749840, 153064792], ![-48124455, -9949211481, 0]], ![![4257152, 879934862, -38266085], ![12031107, 2487295529, 0]]]
    h := ![![![136, 7, 0], ![5, -2, 0]], ![![-66, -4, 0], ![-1, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {65} * I2N0 =  Ideal.span {B.equivFun.symm ![272, 19, -2]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 4225 ![![3, 0, 0], ![-1, 1, 0]]
  ![-5067, -239, 32] ![![4225, 0, 0], ![-1973, 1, 0]] where
    su := ![![12675, 0, 0], ![-4225, 4225, 0]]
    hsu := by decide
    w := ![![-21408075, -1009775, 135200], ![10034375, 473200, -63375]]
    hw := by decide
    g := ![![![1054, 23675, -12], ![2257, 50699, 0]], ![![1823, 191381, -97], ![3904, 409827, 0]]]
    h := ![![![-3684, 2078, -152], ![-5985, 488, 0]], ![![1728, -974, 70], ![2809, -225, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {4225} * I3N0 =  Ideal.span {B.equivFun.symm ![-5067, -239, 32]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 25 ![![5, 0, 0], ![-141, -7, 1]]
  ![-81, -2, 1] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![125, 0, 0], ![-3525, -175, 25]]
    hsu := by decide
    w := ![![-2025, -50, 25], ![1000, 125, 0]]
    hw := by decide
    g := ![![![-21, 4228, 2118], ![190, -52949, 0]], ![![401, -118914, -59552], ![-4711, 1488796, 0]]]
    h := ![![![12, 1, 0], ![1, 0, 0]], ![![8, 1, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {25} * I5N0 =  Ideal.span {B.equivFun.symm ![-81, -2, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 1 ![![5, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![5, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![3, 1, 0], ![-5, 0, 0]], ![![-2, -1, 0], ![6, 0, 0]]]
    h := ![![![3, 1, 0], ![-5, 0, 0]], ![![-2, -1, 0], ![6, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {1} * I5N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 25 ![![7, 0, 0], ![0, 1, 0]]
  ![1379, 68, -9] ![![25, 0, 0], ![2, 1, 0]] where
    su := ![![175, 0, 0], ![0, 25, 0]]
    hsu := by decide
    w := ![![34475, 1700, -225], ![-7700, -375, 50]]
    hw := by decide
    g := ![![![1, 2, 1], ![12, -24, 0]], ![![6, 5, 2], ![8, -48, 0]]]
    h := ![![![197, 9, 0], ![5, -9, 0]], ![![-44, -3, 0], ![6, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {25} * I7N0 =  Ideal.span {B.equivFun.symm ![1379, 68, -9]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS0 


noncomputable def E13RS0 : RelationCertificate Table 169 ![![13, 0, 0], ![-136, -3, 1]]
  ![-961, -110, 2] ![![169, 0, 0], ![55, 1, 0]] where
    su := ![![2197, 0, 0], ![-22984, -507, 169]]
    hsu := by decide
    w := ![![-162409, -18590, 338], ![-50531, -6591, 0]]
    hw := by decide
    g := ![![![-7, -6268, -114], ![38, 19260, 0]], ![![-172, 65713, 1195], ![460, -201930, 0]]]
    h := ![![![83, -5, -1], ![15, 0, 0]], ![![113, 0, -1], ![13, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {169} * I13N0 =  Ideal.span {B.equivFun.symm ![-961, -110, 2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 1 ![![13, 0, 0], ![3, 1, 0]]
  ![1, 0, 0] ![![13, 0, 0], ![3, 1, 0]] where
    su := ![![13, 0, 0], ![3, 1, 0]]
    hsu := by decide
    w := ![![13, 0, 0], ![3, 1, 0]]
    hw := by decide
    g := ![![![16, 5, 0], ![-65, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![16, 5, 0], ![-65, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {1} * I13N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 325 ![![17, 0, 0], ![-4, 1, 0]]
  ![3051, 167, -21] ![![325, 0, 0], ![-23, 1, 0]] where
    su := ![![5525, 0, 0], ![-1300, 325, 0]]
    hsu := by decide
    w := ![![991575, 54275, -6825], ![-94575, -5200, 650]]
    hw := by decide
    g := ![![![-2, -34822, 1514], ![-37, -492052, 0]], ![![23, 7658, -333], ![333, 108226, 0]]]
    h := ![![![4372399, -1144854, 12951], ![18581933, -220188, 0]], ![![-417023, 109195, -1236], ![-1772275, 21014, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {325} * I17N1 =  Ideal.span {B.equivFun.symm ![3051, 167, -21]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 845 ![![19, 0, 0], ![-4, 1, 0]]
  ![14013, 721, -93] ![![845, 0, 0], ![-283, 1, 0]] where
    su := ![![16055, 0, 0], ![-3380, 845, 0]]
    hsu := by decide
    w := ![![11840985, 609245, -78585], ![-4073745, -209560, 27040]]
    hw := by decide
    g := ![![![-21463682, -60228853530, 212823072], ![-64087669, -179835495832, 0]], ![![3837590, 10768133891, -38049991], ![11458526, 32152242390, 0]]]
    h := ![![![19787, -4880, 34], ![90485, -739, 0]], ![![-6803, 1679, -12], ![-31109, 260, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {845} * I19N1 =  Ideal.span {B.equivFun.symm ![14013, 721, -93]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 5 ![![23, 0, 0], ![-9, 1, 0]]
  ![891, 47, -6] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![115, 0, 0], ![-45, 5, 0]]
    hsu := by decide
    w := ![![4455, 235, -30], ![-5190, -275, 35]]
    hw := by decide
    g := ![![![-3, 6, 4], ![3, -21, 0]], ![![-9, -3, -1], ![-1, 5, 0]]]
    h := ![![![43983, -5441, 62], ![112302, -1432, 0]], ![![-51216, 6343, -73], ![-130770, 1686, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {5} * I23N1 =  Ideal.span {B.equivFun.symm ![891, 47, -6]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 169 ![![29, 0, 0], ![-10, 1, 0]]
  ![-1483, -98, 11] ![![169, 0, 0], ![55, 1, 0]] where
    su := ![![4901, 0, 0], ![-1690, 169, 0]]
    hsu := by decide
    w := ![![-250627, -16562, 1859], ![-68783, -4563, 507]]
    hw := by decide
    g := ![![![-934995, 536927484, 9762627], ![2872976, -1649883960, 0]], ![![305981, -175741326, -3195398], ![-940191, 540022260, 0]]]
    h := ![![![-2417, 257, -2], ![-6861, 69, 0]], ![![-653, 74, -1], ![-1853, 32, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {169} * I29N1 =  Ideal.span {B.equivFun.symm ![-1483, -98, 11]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 4225 ![![31, 0, 0], ![10, 1, 0]]
  ![59931, 3127, -401] ![![4225, 0, 0], ![-1973, 1, 0]] where
    su := ![![130975, 0, 0], ![42250, 4225, 0]]
    hsu := by decide
    w := ![![253208475, 13211575, -1694225], ![-118709825, -6193850, 794300]]
    hw := by decide
    g := ![![![-1467408172, -16171513214922, 8196408494], ![-3142321099, -34629825887160, 0]], ![![-566561800, -6243785591227, 3164615245], ![-1213240550, -13370499410124, 0]]]
    h := ![![![1199360961, 143778053, 2384192], ![-3718012986, -73910353, 0]], ![![-562287387, -67406386, -1117763], ![1743088090, 34650841, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4225} * I31N1 =  Ideal.span {B.equivFun.symm ![59931, 3127, -401]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS1 
