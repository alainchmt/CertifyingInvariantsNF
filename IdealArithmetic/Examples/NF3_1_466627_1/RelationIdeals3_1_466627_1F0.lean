import IdealArithmetic.Examples.NF3_1_466627_1.PrimesBelow3_1_466627_1F0
import IdealArithmetic.Examples.NF3_1_466627_1.ClassGroupData3_1_466627_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 32 ![![2, 0, 0], ![-69, -7, 1]]
  ![-87, -5, 1] ![![32, 0, 0], ![4, 1, 0]] where
    su := ![![64, 0, 0], ![-2208, -224, 32]]
    hsu := by decide
    w := ![![-2784, -160, 32], ![64, 0, 0]]
    hw := by decide
    g := ![![![28, -8165, -2043], ![-223, 65376, 0]], ![![-1147, 298757, 74761], ![9193, -2392353, 0]]]
    h := ![![![60, 8, -1], ![3, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {32} * I2N0 =  Ideal.span {B.equivFun.symm ![-87, -5, 1]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0], ![-68, -6, 1]]
  ![-77, -6, 1] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![27, 0, 0], ![-612, -54, 9]]
    hsu := by decide
    w := ![![-693, -54, 9], ![720, 54, -9]]
    hw := by decide
    g := ![![![5449, 132082, -33361], ![12259, 300249, 0]], ![![-119824, -2905815, 733943], ![-269610, -6605487, 0]]]
    h := ![![![65, 6, -1], ![4, 0, 0]], ![![4, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![-77, -6, 1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![-1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![3, 0, 0], ![-1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![-1, 1, 0]]
    hw := by decide
    g := ![![![2, 1, -2], ![3, 6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![2, 1, -2], ![3, 6, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 24 ![![5, 0, 0], ![-71, -8, 1]]
  ![-901, -63, 11] ![![24, 0, 0], ![-4, 1, 0]] where
    su := ![![120, 0, 0], ![-1704, -192, 24]]
    hsu := by decide
    w := ![![-21624, -1512, 264], ![8136, 528, -96]]
    hw := by decide
    g := ![![![4, 29, -7], ![7, 170, 0]], ![![-11, -412, 102], ![-10, -2455, 0]]]
    h := ![![![47, 13, -1], ![16, 0, 0]], ![![11, -2, 0], ![-4, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {24} * I5N0 =  Ideal.span {B.equivFun.symm ![-901, -63, 11]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 72 ![![5, 0, 0], ![2, 1, 0]]
  ![-23, 3, 1] ![![72, 0, 0], ![-4, 1, 0]] where
    su := ![![360, 0, 0], ![144, 72, 0]]
    hsu := by decide
    w := ![![-1656, 216, 72], ![504, 72, 0]]
    hw := by decide
    g := ![![![1, 116, -29], ![4, 2087, 0]], ![![3, 35, -9], ![69, 649, 0]]]
    h := ![![![-1923, -1179, -110], ![4796, 551, 0]], ![![619, 375, 33], ![-1544, -165, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {72} * I5N1 =  Ideal.span {B.equivFun.symm ![-23, 3, 1]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 4 ![![7, 0, 0], ![2, 1, 0]]
  ![91, 5, -1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![28, 0, 0], ![8, 4, 0]]
    hsu := by decide
    w := ![![364, 20, -4], ![-412, -16, 4]]
    hw := by decide
    g := ![![![8, 2, 139], ![3, -555, 0]], ![![17, 5, 56], ![3, -222, 0]]]
    h := ![![![471, 252, 11], ![-1603, -78, 0]], ![![-535, -289, -14], ![1821, 99, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4} * I7N0 =  Ideal.span {B.equivFun.symm ![91, 5, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 32 ![![11, 0, 0], ![-5, 1, 0]]
  ![-55, -5, 1] ![![32, 0, 0], ![4, 1, 0]] where
    su := ![![352, 0, 0], ![-160, 32, 0]]
    hsu := by decide
    w := ![![-1760, -160, 32], ![192, 32, 0]]
    hw := by decide
    g := ![![![1, 160, 40], ![11, -1281, 0]], ![![-5, -49, -12], ![22, 385, 0]]]
    h := ![![![-9885, 2276, -60], ![-21736, 661, 0]], ![![1076, -245, 6], ![2366, -66, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {32} * I11N0 =  Ideal.span {B.equivFun.symm ![-55, -5, 1]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 24 ![![11, 0, 0], ![-4, 1, 0]]
  ![-355, -33, 5] ![![24, 0, 0], ![-4, 1, 0]] where
    su := ![![264, 0, 0], ![-96, 24, 0]]
    hsu := by decide
    w := ![![-8520, -792, 120], ![3480, 312, -48]]
    hw := by decide
    g := ![![![9213121, 1363541565, -341461211], ![55278714, 8195069065, 0]], ![![-4187729, -619784339, 155207818], ![-25126379, -3724987631, 0]]]
    h := ![![![-589, 150, -3], ![-1531, 38, 0]], ![![247, -62, 1], ![643, -13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {24} * I11N1 =  Ideal.span {B.equivFun.symm ![-355, -33, 5]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E11RS1 


noncomputable def E11RS2 : RelationCertificate Table 144 ![![11, 0, 0], ![-3, 1, 0]]
  ![449, 51, -7] ![![144, 0, 0], ![68, 1, 0]] where
    su := ![![1584, 0, 0], ![-432, 144, 0]]
    hsu := by decide
    w := ![![64656, 7344, -1008], ![27648, 3168, -432]]
    hw := by decide
    g := ![![![3780287, -1409832064, -20733642], ![-8005314, 2985644449, 0]], ![![-1374691, 512665104, 7539490], ![2911111, -1085686560, 0]]]
    h := ![![![685, -221, 3], ![2362, -40, 0]], ![![294, -94, 1], ![1014, -14, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N2 : Ideal.span {144} * I11N2 =  Ideal.span {B.equivFun.symm ![449, 51, -7]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E11RS2 


noncomputable def E13RS0 : RelationCertificate Table 6 ![![13, 0, 0], ![-75, -11, 1]]
  ![-55, -15, -1] ![![6, 0, 0], ![2, 1, 0]] where
    su := ![![78, 0, 0], ![-450, -66, 6]]
    hsu := by decide
    w := ![![-330, -90, -6], ![-522, -192, -18]]
    hw := by decide
    g := ![![![472, -9264, -4748], ![-1383, 28487, 0]], ![![-2651, 53458, 27397], ![8032, -164384, 0]]]
    h := ![![![65, 9, -1], ![12, 0, 0]], ![![51, 6, -1], ![10, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {6} * I13N0 =  Ideal.span {B.equivFun.symm ![-55, -15, -1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 288 ![![13, 0, 0], ![-3, 1, 0]]
  ![865, 291, 25] ![![288, 0, 0], ![68, 1, 0]] where
    su := ![![3744, 0, 0], ![-864, 288, 0]]
    hsu := by decide
    w := ![![249120, 83808, 7200], ![69120, 23328, 2016]]
    hw := by decide
    g := ![![![-403902455, 520131276603, 7649076711], ![1710645677, -2202934092756, 0]], ![![103563609, -133365577524, -1961280890], ![-438622335, 564848896313, 0]]]
    h := ![![![838303, -291903, 4173], ![3632358, -54224, 0]], ![![232590, -80987, 1157], ![1007810, -15034, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {288} * I13N1 =  Ideal.span {B.equivFun.symm ![865, 291, 25]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![-7, 1, 0]]
  ![37, 12, 1] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![51, 0, 0], ![-21, 3, 0]]
    hsu := by decide
    w := ![![111, 36, 3], ![375, 132, 12]]
    hw := by decide
    g := ![![![-282, -1998, 2180], ![-569, -6536, 0]], ![![134, 703, -761], ![191, 2280, 0]]]
    h := ![![![122, -16, 0], ![291, 1, 0]], ![![394, -58, 1], ![939, -13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![37, 12, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-6, 1, 0]]
  ![31, 11, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![38, 0, 0], ![-12, 2, 0]]
    hsu := by decide
    w := ![![62, 22, 2], ![412, 138, 12]]
    hw := by decide
    g := ![![![87, 9, 1086], ![5, -2175, 0]], ![![-60, -6, -299], ![-3, 600, 0]]]
    h := ![![![379, -62, 0], ![1195, 1, 0]], ![![2474, -441, 6], ![7800, -108, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![31, 11, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 16 ![![23, 0, 0], ![-6, 1, 0]]
  ![-157, -55, -5] ![![16, 0, 0], ![4, 1, 0]] where
    su := ![![368, 0, 0], ![-96, 16, 0]]
    hsu := by decide
    w := ![![-2512, -880, -80], ![-2688, -912, -80]]
    hw := by decide
    g := ![![![6553, -448557, -112550], ![-26393, 1800810, 0]], ![![-1554, 107009, 26850], ![6308, -429605, 0]]]
    h := ![![![-227, 39, -1], ![-844, 18, 0]], ![![-240, 41, -1], ![-892, 18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {16} * I23N1 =  Ideal.span {B.equivFun.symm ![-157, -55, -5]} * (J0 ^ 4*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_0 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 6 ![![29, 0, 0], ![-14, 1, 0]]
  ![-41, -9, 1] ![![6, 0, 0], ![2, 1, 0]] where
    su := ![![174, 0, 0], ![-84, 6, 0]]
    hsu := by decide
    w := ![![-246, -54, 6], ![330, 48, -6]]
    hw := by decide
    g := ![![![6, -7, -4], ![5, 25, 0]], ![![-3, 3, 2], ![5, -12, 0]]]
    h := ![![![-3541, 309, -4], ![-7332, 117, 0]], ![![4815, -400, 4], ![9970, -117, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {6} * I29N1 =  Ideal.span {B.equivFun.symm ![-41, -9, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS1 
