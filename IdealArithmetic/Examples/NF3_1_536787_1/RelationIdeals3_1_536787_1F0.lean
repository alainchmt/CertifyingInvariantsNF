import IdealArithmetic.Examples.NF3_1_536787_1.PrimesBelow3_1_536787_1F0
import IdealArithmetic.Examples.NF3_1_536787_1.ClassGroupData3_1_536787_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 8 ![![2, 0, 0], ![1, 1, 1]]
  ![25, 5, 1] ![![8, 0, 0], ![3, 1, 0]] where
    su := ![![16, 0, 0], ![8, 8, 8]]
    hsu := by decide
    w := ![![200, 40, 8], ![216, 40, 8]]
    hw := by decide
    g := ![![![-1, 9, 3], ![1, -24, 0]], ![![7, 6, 2], ![4, -18, 0]]]
    h := ![![![10, 0, -2], ![5, 0, 0]], ![![11, 0, -2], ![5, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {8} * I2N0 =  Ideal.span {B.equivFun.symm ![25, 5, 1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E2RS0 


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

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![1, 1, 1]]
  ![1, 0, 0] ![![5, 0, 0], ![1, 1, 1]] where
    su := ![![5, 0, 0], ![1, 1, 1]]
    hsu := by decide
    w := ![![5, 0, 0], ![1, 1, 1]]
    hw := by decide
    g := ![![![0, -1, -1], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, -1], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![-1, 1, 0]]
  ![1192, 229, 44] ![![5, 0, 0], ![1, 1, 1]] where
    su := ![![25, 0, 0], ![-5, 5, 0]]
    hsu := by decide
    w := ![![5960, 1145, 220], ![39685, 7625, 1465]]
    hw := by decide
    g := ![![![28, 0, -3], ![8, 0, 0]], ![![-44, 7, 2], ![-7, 0, 0]]]
    h := ![![![530, -256, 19], ![1458, -51, 0]], ![![3528, -1703, 126], ![9703, -337, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![1192, 229, 44]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![3, 1, 0]]
  ![120091, 23073, 4433] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![14, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![240182, 46146, 8866], ![745144, 143164, 27506]]
    hw := by decide
    g := ![![![71, 55, -8], ![64, -21, 0]], ![![-283, 96, 6], ![-91, -6, 0]]]
    h := ![![![327223, 137518, 10922], ![-723490, -72021, 0]], ![![1015184, 426646, 33887], ![-2244572, -223456, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![120091, 23073, 4433]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 10 ![![7, 0, 0], ![-2, 1, 0]]
  ![-1, -5, 1] ![![10, 0, 0], ![-4, 1, 1]] where
    su := ![![70, 0, 0], ![-20, 10, 0]]
    hsu := by decide
    w := ![![-10, -50, 10], ![-560, 160, -10]]
    hw := by decide
    g := ![![![-1588, -3, -75], ![630, 133, 0]], ![![709, 8, 34], ![-277, -57, 0]]]
    h := ![![![-13, 8, -1], ![-45, 8, 0]], ![![-1336, 706, -20], ![-4648, 139, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {10} * I7N1 =  Ideal.span {B.equivFun.symm ![-1, -5, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 20 ![![7, 0, 0], ![-1, 1, 0]]
  ![-29, -5, -1] ![![20, 0, 0], ![6, 1, 1]] where
    su := ![![140, 0, 0], ![-20, 20, 0]]
    hsu := by decide
    w := ![![-580, -100, -20], ![-1020, -200, -40]]
    hw := by decide
    g := ![![![-131, -4, 1], ![-39, 20, 0]], ![![2, -1, -1], ![21, -1, 0]]]
    h := ![![![-8, 4, -1], ![-27, 6, 0]], ![![-16, 8, -1], ![-61, 5, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {20} * I7N2 =  Ideal.span {B.equivFun.symm ![-29, -5, -1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS2 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0], ![5, 4, 1]]
  ![-1096423, -210655, -40473] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![22, 0, 0], ![10, 8, 2]]
    hsu := by decide
    w := ![![-2192846, -421310, -80946], ![-6803116, -1307078, -251128]]
    hw := by decide
    g := ![![![387, -209, -215], ![89, 387, 0]], ![![-414, -71, -46], ![-241, 172, 0]]]
    h := ![![![-81928, -4953, -130], ![-39043, 0, 0]], ![![-254168, -15361, -402], ![-121142, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![-1096423, -210655, -40473]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 8 ![![11, 0, 0], ![-4, 1, 0]]
  ![-281, -149, 39] ![![8, 0, 0], ![3, 1, 0]] where
    su := ![![88, 0, 0], ![-32, 8, 0]]
    hsu := by decide
    w := ![![-2248, -1192, 312], ![4656, -728, -32]]
    hw := by decide
    g := ![![![-12220, -2121, -528], ![-4843, 79, 0]], ![![-1339, -221, -54], ![-529, -22, 0]]]
    h := ![![![-455, 108, 0], ![-1181, 39, 0]], ![![978, -257, 4], ![2544, -48, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {8} * I11N1 =  Ideal.span {B.equivFun.symm ![-281, -149, 39]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E11RS1 


noncomputable def E17RS1 : RelationCertificate Table 20 ![![17, 0, 0], ![6, 1, 0]]
  ![-19, 165, -31] ![![20, 0, 0], ![6, 1, 1]] where
    su := ![![340, 0, 0], ![120, 20, 0]]
    hsu := by decide
    w := ![![-380, 3300, -620], ![18780, -3400, -40]]
    hw := by decide
    g := ![![![62044, 598, -720], ![18613, -10872, 0]], ![![38496, 319, -457], ![11546, -6795, 0]]]
    h := ![![![-17, 0, -3], ![45, 20, 0]], ![![921, 153, 3], ![-2453, -53, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {20} * I17N1 =  Ideal.span {B.equivFun.symm ![-19, 165, -31]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E17RS1 


noncomputable def E19RS0 : RelationCertificate Table 20 ![![19, 0, 0], ![5, 1, 0]]
  ![2909, -231, -63] ![![20, 0, 0], ![6, 1, 1]] where
    su := ![![380, 0, 0], ![100, 20, 0]]
    hsu := by decide
    w := ![![58180, -4620, -1260], ![-24000, -7360, 2300]]
    hw := by decide
    g := ![![![73412, 14259, 1817], ![22836, -19, 0]], ![![39388, 7657, 976], ![12257, -4, 0]]]
    h := ![![![2871, 568, 4], ![-10328, -139, 0]], ![![-1200, -262, 3], ![4320, 58, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {20} * I19N0 =  Ideal.span {B.equivFun.symm ![2909, -231, -63]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E19RS0 


noncomputable def E19RS1 : RelationCertificate Table 8 ![![19, 0, 0], ![-3, 1, 0]]
  ![129085, 24801, 4765] ![![8, 0, 0], ![3, 1, 0]] where
    su := ![![152, 0, 0], ![-24, 8, 0]]
    hsu := by decide
    w := ![![1032680, 198408, 38120], ![1059120, 203488, 39096]]
    hw := by decide
    g := ![![![-2754813617, 67033802447, 22650691236], ![7346170202, -181205529941, 0]], ![![579960699, -14112378813, -4768566361], ![-1546562083, 38148530894, 0]]]
    h := ![![![3261745, -1107769, 8281], ![20614690, -152574, 0]], ![![3345252, -1136130, 8493], ![21142466, -156480, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {8} * I19N1 =  Ideal.span {B.equivFun.symm ![129085, 24801, 4765]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E19RS1 


noncomputable def E19RS2 : RelationCertificate Table 40 ![![19, 0, 0], ![-2, 1, 0]]
  ![1367, 1075, -257] ![![40, 0, 0], ![-14, 1, 1]] where
    su := ![![760, 0, 0], ![-80, 40, 0]]
    hsu := by decide
    w := ![![54680, 43000, -10280], ![96200, -49920, 6040]]
    hw := by decide
    g := ![![![115285, 25345, 5709], ![-39551, -441, 0]], ![![19148, 4306, 957], ![-6531, 24, 0]]]
    h := ![![![117839, -59418, 282], ![1118787, -5615, 0]], ![![210025, -106053, 527], ![1994035, -9862, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {40} * I19N2 =  Ideal.span {B.equivFun.symm ![1367, 1075, -257]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E19RS2 


noncomputable def E23RS1 : RelationCertificate Table 4 ![![23, 0, 0], ![11, 1, 0]]
  ![-515, -99, -19] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![92, 0, 0], ![44, 4, 0]]
    hsu := by decide
    w := ![![-2060, -396, -76], ![-2164, -416, -80]]
    hw := by decide
    g := ![![![2, 25, -23], ![9, 88, 0]], ![![-5, 12, -11], ![5, 43, 0]]]
    h := ![![![-6609, -979, -35], ![13772, 786, 0]], ![![-6943, -1031, -37], ![14468, 831, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {4} * I23N1 =  Ideal.span {B.equivFun.symm ![-515, -99, -19]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 40 ![![29, 0, 0], ![9, 1, 0]]
  ![831643, 159783, 30699] ![![40, 0, 0], ![-14, 1, 1]] where
    su := ![![1160, 0, 0], ![360, 40, 0]]
    hsu := by decide
    w := ![![33265720, 6391320, 1227960], ![15214960, 2923240, 561640]]
    hw := by decide
    g := ![![![700, -31, 8], ![-215, -276, 0]], ![![242, -21, 5], ![-71, -99, 0]]]
    h := ![![![2540726, 316841, 4638], ![-8094379, -103803, 0]], ![![1162070, 144913, 2121], ![-3702184, -47468, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {40} * I29N1 =  Ideal.span {B.equivFun.symm ![831643, 159783, 30699]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E29RS1 
