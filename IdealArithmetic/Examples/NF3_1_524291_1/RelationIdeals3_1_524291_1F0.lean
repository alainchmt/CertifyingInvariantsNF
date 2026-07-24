import IdealArithmetic.Examples.NF3_1_524291_1.PrimesBelow3_1_524291_1F0
import IdealArithmetic.Examples.NF3_1_524291_1.ClassGroupData3_1_524291_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 8 ![![2, 0, 0], ![0, 1, 0]]
  ![-354, 31, 4] ![![8, 0, 0], ![-1, 1, 0]] where
    su := ![![16, 0, 0], ![0, 8, 0]]
    hsu := by decide
    w := ![![-2832, 248, 32], ![976, -416, 128]]
    hw := by decide
    g := ![![![712, 84, 44], ![-79, 0, 0]], ![![54654, -51141, 106428], ![-13223, -212471, -2]]]
    h := ![![![-148, 24, 60], ![-46, -29, 0]], ![![61, -21, 8], ![-10, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {8} * I2N0 =  Ideal.span {B.equivFun.symm ![-354, 31, 4]} * (J0 ^ 3*J1^ 0) := by
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


noncomputable def E5RS0 : RelationCertificate Table 56 ![![5, 0, 0], ![2, 1, 0]]
  ![-2466, -393, 284] ![![56, 0, 0], ![-1, 1, 0]] where
    su := ![![280, 0, 0], ![112, 56, 0]]
    hsu := by decide
    w := ![![-138096, -22008, 15904], ![41440, -1680, -1288]]
    hw := by decide
    g := ![![![-28767307662906347, 28767306886521122, -57571306772559374], ![1027403831239821, 805998294738196536, 310556359]], ![![-11506902352708603, 11506902042164986, -23028481257715487], ![410960792765648, 322398737576970666, 124222320]]]
    h := ![![![-26836, -13250, -63332], ![-13379, 79236, 0]], ![![2266, 1053, 5129], ![1122, -6417, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {56} * I5N0 =  Ideal.span {B.equivFun.symm ![-2466, -393, 284]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 2 ![![5, 0, 0], ![-2, 1, 0]]
  ![74452, 7645, 4538] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![10, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![148904, 15290, 9076], ![725062, 74452, 44194]]
    hw := by decide
    g := ![![![10285, -2070, 245], ![4110, 0, -171]], ![![-2628, 591, -69], ![-1016, 0, 38]]]
    h := ![![![99646, -153856, 226922], ![-70629, -282518, 0]], ![![485209, -749175, 1104957], ![-343915, -1375672, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {2} * I5N1 =  Ideal.span {B.equivFun.symm ![74452, 7645, 4538]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E5RS2 : RelationCertificate Table 448 ![![5, 0, 0], ![-1, 1, 0]]
  ![114, 1, -4] ![![448, 0, 0], ![-113, 1, 0]] where
    su := ![![2240, 0, 0], ![-448, 448, 0]]
    hsu := by decide
    w := ![![51072, 448, -1792], ![-13440, 0, 448]]
    hw := by decide
    g := ![![![11385562983312, -713141245428569, 25022840503799], ![-4463638085793, -2802559136755129, -36047915]], ![![-2276999533128, 142621167288098, -5004319613250], ![892683291417, 560483996739994, 7209225]]]
    h := ![![![3339, -3316, 7164], ![-1331, -8956, 0]], ![![-835, 829, -1791], ![333, 2239, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {448} * I5N2 =  Ideal.span {B.equivFun.symm ![114, 1, -4]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 224 ![![7, 0, 0], ![2, 1, 0]]
  ![-650, 179, -44] ![![224, 0, 0], ![111, 1, 0]] where
    su := ![![1568, 0, 0], ![448, 224, 0]]
    hsu := by decide
    w := ![![-145600, 40096, -9856], ![-77952, 19040, -4256]]
    hw := by decide
    g := ![![![-604272603212, -47194176203278, -1715380220979], ![-510126942537, 96109141786158, -1693784469]], ![![-172649269647, -13484046785271, -490108505221], ![-145750516470, 27459747549255, -483938292]]]
    h := ![![![-66, 39, 44], ![-6, -88, 0]], ![![-38, 18, 19], ![-3, -38, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {224} * I7N0 =  Ideal.span {B.equivFun.symm ![-650, 179, -44]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![-2, 1, 0]]
  ![-476, 83, -12] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![14, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-952, 166, -24], ![-1990, -476, 296]]
    hw := by decide
    g := ![![![53676, -4382, 4471], ![24647, 0, 162]], ![![60769, -6038, 4538], ![27366, 0, 0]]]
    h := ![![![-1188, 1867, -2592], ![613, 4533, 0]], ![![-2181, 3340, -4688], ![1105, 8241, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![-476, 83, -12]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 16 ![![7, 0, 0], ![-1, 1, 0]]
  ![-354, 31, 4] ![![112, 0, 0], ![-1, 1, 0]] where
    su := ![![112, 0, 0], ![-16, 16, 0]]
    hsu := by decide
    w := ![![-39648, 3472, 448], ![976, -416, 128]]
    hw := by decide
    g := ![![![3041, -2643, 5383], ![-49, -150108, 0]], ![![-79, 519, -933], ![71, 26805, 0]]]
    h := ![![![-361, 38, -28], ![63, 56, 0]], ![![5, 0, -8], ![6, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {16} * I7N2 =  Ideal.span {B.equivFun.symm ![-354, 31, 4]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS2 


noncomputable def E11RS0 : RelationCertificate Table 2 ![![11, 0, 0], ![1, 3, 1]]
  ![2, -5, 2] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![22, 0, 0], ![2, 6, 2]]
    hsu := by decide
    w := ![![4, -10, 4], ![272, 2, -14]]
    hw := by decide
    g := ![![![-1945, 387, -51], ![-779, 0, 33]], ![![-263, 43, -11], ![-108, 0, 3]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![12, -1, -1], ![4, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {2} * I11N0 =  Ideal.span {B.equivFun.symm ![2, -5, 2]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 8 ![![11, 0, 0], ![-3, 1, 0]]
  ![22, 7, -4] ![![8, 0, 0], ![-1, 1, 0]] where
    su := ![![88, 0, 0], ![-24, 8, 0]]
    hsu := by decide
    w := ![![176, 56, -32], ![-568, 8, 24]]
    hw := by decide
    g := ![![![2037016321, -2036788992, 4200886037], ![-509225664, -8401768821, -12987]], ![![-385381586, 385338618, -794762544], ![96340032, 1589524477, 2457]]]
    h := ![![![74, -157, 160], ![-30, -441, 0]], ![![-244, 532, -543], ![125, 1494, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {8} * I11N1 =  Ideal.span {B.equivFun.symm ![22, 7, -4]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E11RS1 


noncomputable def E17RS1 : RelationCertificate Table 56 ![![17, 0, 0], ![-5, 1, 0]]
  ![1902, 195, 116] ![![56, 0, 0], ![-1, 1, 0]] where
    su := ![![952, 0, 0], ![-280, 56, 0]]
    hsu := by decide
    w := ![![106512, 10920, 6496], ![14728, 1512, 896]]
    hw := by decide
    g := ![![![1606302254, -1606302223, 3214653300], ![-57367887, -45005146200, -12]], ![![-102750, 102748, -205628], ![3693, 2878794, 0]]]
    h := ![![![1836906, -6258465, 4207948], ![-908400, -17883750, 0]], ![![253999, -865381, 581848], ![-125596, -2472850, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {56} * I17N1 =  Ideal.span {B.equivFun.symm ![1902, 195, 116]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 4 ![![19, 0, 0], ![9, 1, 0]]
  ![-10, 1, 0] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![76, 0, 0], ![36, 4, 0]]
    hsu := by decide
    w := ![![-40, 4, 0], ![12, -12, 4]]
    hw := by decide
    g := ![![![-450717, -26514, -3409], ![106054, 0, 13635]], ![![-250400, -14730, -1894], ![58918, 0, 7575]]]
    h := ![![![-109, -572, -288], ![-75, 1368, 0]], ![![30, 180, 91], ![33, -432, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {4} * I19N1 =  Ideal.span {B.equivFun.symm ![-10, 1, 0]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 112 ![![23, 0, 0], ![7, 1, 0]]
  ![-1161110, -119227, -70772] ![![112, 0, 0], ![-1, 1, 0]] where
    su := ![![2576, 0, 0], ![784, 112, 0]]
    hsu := by decide
    w := ![![-130044320, -13353424, -7926464], ![-8985424, -922656, -547680]]
    hw := by decide
    g := ![![![-60396255021011161, 60396255020212677, -120811769050322824], ![1078504553939591, 3382729533408879302, 638786]], ![![-21430929201069442, 21430929200786093, -42868692243793891], ![382695164302329, 1200323382826172288, 226666]]]
    h := ![![![4346253, 14898540, 9989856], ![1970543, -57459365, 0]], ![![300298, 1029415, 690250], ![136177, -3970160, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {112} * I23N1 =  Ideal.span {B.equivFun.symm ![-1161110, -119227, -70772]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 2 ![![29, 0, 0], ![3, 1, 0]]
  ![886, 91, 54] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![58, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![1772, 182, 108], ![8628, 886, 526]]
    hw := by decide
    g := ![![![5058, -1020, 136], ![2019, 0, -87]], ![![544, -111, 13], ![219, 0, -9]]]
    h := ![![![-29782, -30093, -60474], ![-4112, 438450, 0]], ![![-145010, -146525, -294453], ![-20032, 2134850, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {2} * I29N0 =  Ideal.span {B.equivFun.symm ![886, 91, 54]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 4 ![![29, 0, 0], ![-7, 1, 0]]
  ![262, 27, 16] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![116, 0, 0], ![-28, 4, 0]]
    hsu := by decide
    w := ![![1048, 108, 64], ![2032, 208, 124]]
    hw := by decide
    g := ![![![392933714, 23113747, 2971769], ![-92454989, 0, -11887071]], ![![-94846525, -5579209, -717327], ![22316833, 0, 2869307]]]
    h := ![![![-6874, 30045, -15068], ![2698, 109247, 0]], ![![-13327, 58265, -29221], ![5247, 211860, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {4} * I29N1 =  Ideal.span {B.equivFun.symm ![262, 27, 16]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 224 ![![31, 0, 0], ![4, 1, 0]]
  ![110, -1, 4] ![![224, 0, 0], ![111, 1, 0]] where
    su := ![![6944, 0, 0], ![896, 224, 0]]
    hsu := by decide
    w := ![![24640, -224, 896], ![12768, 0, 448]]
    hw := by decide
    g := ![![![2947, 227735, 8319], ![2503, -463774, -74]], ![![453, 36929, 1349], ![456, -75205, -12]]]
    h := ![![![-666, -1020, -1364], ![-97, 10572, 0]], ![![-345, -528, -706], ![-48, 5472, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {224} * I31N1 =  Ideal.span {B.equivFun.symm ![110, -1, 4]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E31RS1 
