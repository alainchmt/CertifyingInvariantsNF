import IdealArithmetic.Examples.NF3_1_369800_2.PrimesBelow3_1_369800_2F1
import IdealArithmetic.Examples.NF3_1_369800_2.ClassGroupData3_1_369800_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 98 ![![37, 0, 0], ![14, 1, 0]]
  ![-18469, -5227, -789] ![![98, 0, 0], ![-44, -3, 1]] where
    su := ![![3626, 0, 0], ![1372, 98, 0]]
    hsu := by decide
    w := ![![-1809962, -512246, -77322], ![-263914, -74676, -11270]]
    hw := by decide
    g := ![![![-4670601464138, -403570692788, 65166044075], ![2110023903624, 1699259244579, 0]], ![![-1735696453741, -149975592155, 24217110467], ![784130488346, 631481462821, 0]]]
    h := ![![![-10454245, -194971543, -27888697], ![-9225136, 515940500, 0]], ![![-1524371, -28429389, -4066535], ![-1345129, 75230840, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {98} * I37N1 =  Ideal.span {B.equivFun.symm ![-18469, -5227, -789]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E37RS1 


noncomputable def E43RS0 : RelationCertificate Table 14 ![![43, 0, 0], ![14, 1, 0]]
  ![-2273, -195, 50] ![![14, 0, 0], ![-41, -4, 1]] where
    su := ![![602, 0, 0], ![196, 14, 0]]
    hsu := by decide
    w := ![![-31822, -2730, 700], ![-25242, -1008, 392]]
    hw := by decide
    g := ![![![23378417511, 1227802710, 41165087], ![-68813225915, -9747880472, 67368]], ![![8349434820, 438500985, 14701822], ![-24576152043, -3481385870, 24060]]]
    h := ![![![8476, 147543, 21100], ![6206, -453625, 0]], ![![6729, 117171, 16756], ![4935, -360240, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {14} * I43N0 =  Ideal.span {B.equivFun.symm ![-2273, -195, 50]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E43RS0 


noncomputable def E53RS1 : RelationCertificate Table 49 ![![53, 0, 0], ![22, 1, 0]]
  ![-9874, -2795, -422] ![![49, 0, 0], ![-24, 1, 0]] where
    su := ![![2597, 0, 0], ![1078, 49, 0]]
    hsu := by decide
    w := ![![-483826, -136955, -20678], ![96187, 27244, 4116]]
    hw := by decide
    g := ![![![1996588, -78100083, 6512716], ![-2571754, -159561468, 0]], ![![847059, -33133367, 2762970], ![-1091043, -67692744, 0]]]
    h := ![![![74820, 2334907, 212390], ![75146, -5628546, 0]], ![![-14895, -464190, -42224], ![-14890, 1118978, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {49} * I53N1 =  Ideal.span {B.equivFun.symm ![-9874, -2795, -422]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E53RS1 


noncomputable def E61RS1 : RelationCertificate Table 14 ![![61, 0, 0], ![-20, 1, 0]]
  ![493, 327, -51] ![![14, 0, 0], ![-44, -3, 1]] where
    su := ![![854, 0, 0], ![-280, 14, 0]]
    hsu := by decide
    w := ![![6902, 4578, -714], ![124138, 8064, -2366]]
    hw := by decide
    g := ![![![-1164, -2088, -599], ![4097, 218, 0]], ![![203, 217, 61], ![-647, -60, 0]]]
    h := ![![![-103, 3025, -303], ![122, 9216, 0]], ![![-2613, 68239, -6829], ![1997, 208200, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {14} * I61N1 =  Ideal.span {B.equivFun.symm ![493, 327, -51]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E61RS1 


noncomputable def E67RS0 : RelationCertificate Table 49 ![![67, 0, 0], ![-26, 1, 0]]
  ![3470, 111, -50] ![![49, 0, 0], ![-24, 1, 0]] where
    su := ![![3283, 0, 0], ![-1274, 49, 0]]
    hsu := by decide
    w := ![![170030, 5439, -2450], ![-99519, -2744, 1372]]
    hw := by decide
    g := ![![![4072156, -159286240, 13282764], ![-5245209, -325427872, 0]], ![![-1560023, 61021659, -5088554], ![2009467, 124669600, 0]]]
    h := ![![![-21928, 773946, -59558], ![20097, 1995168, 0]], ![![12869, -453105, 34868], ![-11685, -1168064, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {49} * I67N0 =  Ideal.span {B.equivFun.symm ![3470, 111, -50]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E67RS0 


noncomputable def E67RS1 : RelationCertificate Table 98 ![![67, 0, 0], ![-22, 1, 0]]
  ![309805, 87671, 13233] ![![98, 0, 0], ![-44, -3, 1]] where
    su := ![![6566, 0, 0], ![-2156, 98, 0]]
    hsu := by decide
    w := ![![30360890, 8591758, 1296834], ![4425778, 1252440, 189042]]
    hw := by decide
    g := ![![![33176, 2859, -466], ![-14963, -11868, 0]], ![![-10525, -906, 148], ![4779, 3748, 0]]]
    h := ![![![-66352047, 1811861418, -164780613], ![48830009, 5520157152, 0]], ![![-9672279, 264119294, -24020457], ![7118110, 804686274, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {98} * I67N1 =  Ideal.span {B.equivFun.symm ![309805, 87671, 13233]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E67RS1 


noncomputable def E67RS2 : RelationCertificate Table 98 ![![67, 0, 0], ![-20, 1, 0]]
  ![-81429, -23043, -3478] ![![98, 0, 0], ![-69, -4, 1]] where
    su := ![![6566, 0, 0], ![-1960, 98, 0]]
    hsu := by decide
    w := ![![-7980042, -2258214, -340844], ![2032814, 575260, 86828]]
    hw := by decide
    g := ![![![1226157605517042, -23857308250464, -30933507170762], ![-862656929130967, -556305804214518, -1181790]], ![![-354223308260353, 6892111272355, 8936346515995], ![249212001748925, 160710565661922, 341406]]]
    h := ![![![64568810, -1543363378, 154399400], ![-42309497, -5172381639, 0]], ![![-16448051, 393151976, -39331262], ![10777878, 1317597720, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N2 : Ideal.span {98} * I67N2 =  Ideal.span {B.equivFun.symm ![-81429, -23043, -3478]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E67RS2 


noncomputable def E71RS1 : RelationCertificate Table 14 ![![71, 0, 0], ![-8, 1, 0]]
  ![-2273, -643, -97] ![![14, 0, 0], ![-44, -3, 1]] where
    su := ![![994, 0, 0], ![-112, 14, 0]]
    hsu := by decide
    w := ![![-31822, -9002, -1358], ![-32466, -9184, -1386]]
    hw := by decide
    g := ![![![-262844, -61832, -15167], ![838361, 125226, 0]], ![![-43823, -10306, -2528], ![139768, 20871, 0]]]
    h := ![![![1912774, -15689751, 3923971], ![-436474, -139301019, 0]], ![![1951485, -16007275, 4003383], ![-445299, -142120146, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {14} * I71N1 =  Ideal.span {B.equivFun.symm ![-2273, -643, -97]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E71RS1 


noncomputable def E79RS1 : RelationCertificate Table 14 ![![79, 0, 0], ![-28, 1, 0]]
  ![-4237, -43, 48] ![![14, 0, 0], ![-41, -4, 1]] where
    su := ![![1106, 0, 0], ![-392, 14, 0]]
    hsu := by decide
    w := ![![-59318, -602, 672], ![106596, 11578, -2688]]
    hw := by decide
    g := ![![![-1683008530252, -88395335628, -2964139599], ![4953854781751, 701764702194, -150348]], ![![594003010770, 31198353925, 1046166974], ![-1748419334952, -247681659591, 53064]]]
    h := ![![![1422809, -51270418, 3663216], ![-1153245, -144697008, 0]], ![![-2548680, 91841546, -6561980], ![2065885, 259198114, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {14} * I79N1 =  Ideal.span {B.equivFun.symm ![-4237, -43, 48]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E79RS1 
