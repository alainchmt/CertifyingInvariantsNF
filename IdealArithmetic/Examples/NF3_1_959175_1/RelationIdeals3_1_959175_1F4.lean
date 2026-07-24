import IdealArithmetic.Examples.NF3_1_959175_1.PrimesBelow3_1_959175_1F4
import IdealArithmetic.Examples.NF3_1_959175_1.ClassGroupData3_1_959175_1

set_option linter.all false

noncomputable section


noncomputable def E227RS1 : RelationCertificate Table 4 ![![227, 0, 0], ![50, 1, 0]]
  ![157988, 45958, 6925] ![![4, 0, 0], ![-33, -2, 1]] where
    su := ![![908, 0, 0], ![200, 4, 0]]
    hsu := by decide
    w := ![![631952, 183832, 27700], ![1837636, 534560, 80548]]
    hw := by decide
    g := ![![![627140, 42834, 509111], ![-5068037, -606210, 0]], ![![139868223834, 9501172667, 113557284238], ![-1130274111638, -135208994917, 0]]]
    h := ![![![20521544, 438988, 1143], ![-93164650, -126268, 0]], ![![59674117, 1276556, 3325], ![-270911303, -367319, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R227N1 : Ideal.span {4} * I227N1 =  Ideal.span {B.equivFun.symm ![157988, 45958, 6925]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E227RS1 


noncomputable def E229RS1 : RelationCertificate Table 4 ![![229, 0, 0], ![-4, 1, 0]]
  ![-4, 1, 0] ![![4, 0, 0], ![-69, -3, 2]] where
    su := ![![916, 0, 0], ![-16, 4, 0]]
    hsu := by decide
    w := ![![-16, 4, 0], ![836, 44, -16]]
    hw := by decide
    g := ![![![64, 5, -2], ![5, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-60, 18, -2], ![-3434, 229, 0]], ![![3161, -790, 0], ![180915, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R229N1 : Ideal.span {4} * I229N1 =  Ideal.span {B.equivFun.symm ![-4, 1, 0]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E229RS1 


noncomputable def E233RS1 : RelationCertificate Table 2 ![![233, 0, 0], ![28, 1, 0]]
  ![48522, -4365, 73] ![![2, 0, 0], ![-35, -1, 1]] where
    su := ![![466, 0, 0], ![56, 2, 0]]
    hsu := by decide
    w := ![![97044, -8730, 146], ![-2961350, -113836, 63004]]
    hw := by decide
    g := ![![![581909, -50747007, -13508001], ![8436539, -372400, 0]], ![![92869, -8846623, -2381453], ![1607770, -45619, 0]]]
    h := ![![![75410, 2735, 5], ![-625786, -546, 0]], ![![-2312303, -85024, -32], ![19188783, 19479, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {2} * I233N1 =  Ideal.span {B.equivFun.symm ![48522, -4365, 73]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E233RS1 


noncomputable def E239RS1 : RelationCertificate Table 4 ![![239, 0, 0], ![-71, 1, 0]]
  ![2504856468, 728651184, 109793887] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![956, 0, 0], ![-284, 4, 0]]
    hsu := by decide
    w := ![![10019425872, 2914604736, 439175548], ![33247144828, 9671440960, 1457302368]]
    hw := by decide
    g := ![![![719958, 36614, -25976], ![189145, 0, 0]], ![![-242505, -11158, 8531], ![-63413, -7, 0]]]
    h := ![![![272945175118, -3924966580, 2855523], ![918751999954, -286338055, 0]], ![![905705364962, -13024092799, 9475392], ![3048665780841, -950146548, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {4} * I239N1 =  Ideal.span {B.equivFun.symm ![2504856468, 728651184, 109793887]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E239RS1 


noncomputable def E241RS0 : RelationCertificate Table 2 ![![241, 0, 0], ![105, 1, 0]]
  ![-8142, -633, 230] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![482, 0, 0], ![210, 2, 0]]
    hsu := by decide
    w := ![![-16284, -1266, 460], ![56258, 2552, -1266]]
    hw := by decide
    g := ![![![1919654, 185266, 107209], ![1052461, 0, 0]], ![![934123, 90152, 52169], ![512139, 0, 0]]]
    h := ![![![143418, 783, -10], ![-329256, 1320, 0]], ![![-496796, -2839, 33], ![1140533, -4293, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N0 : Ideal.span {2} * I241N0 =  Ideal.span {B.equivFun.symm ![-8142, -633, 230]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E241RS0 


noncomputable def E241RS1 : RelationCertificate Table 4 ![![241, 0, 0], ![-58, 1, 0]]
  ![-1605516, -207517, 60025] ![![4, 0, 0], ![35, 3, -1]] where
    su := ![![964, 0, 0], ![-232, 4, 0]]
    hsu := by decide
    w := ![![-6422064, -830068, 240100], ![69139700, 609740, -1107628]]
    hw := by decide
    g := ![![![71199414, -5866415279, -2071870794], ![-3258848619, 2158800, 0]], ![![-13623957, 1113331500, 393090707], ![617516586, -512715, 0]]]
    h := ![![![-385256824, 6962580, -11021], ![-1600780846, 1358043, 0]], ![![4148470725, -74980823, 120161], ![17237313100, -14617854, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {4} * I241N1 =  Ideal.span {B.equivFun.symm ![-1605516, -207517, 60025]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E241RS1 


noncomputable def E241RS2 : RelationCertificate Table 4 ![![241, 0, 0], ![-47, 1, 0]]
  ![-20236, -1130, 493] ![![4, 0, 0], ![-33, -2, 1]] where
    su := ![![964, 0, 0], ![-188, 4, 0]]
    hsu := by decide
    w := ![![-80944, -4520, 1972], ![-62732, 26192, -3740]]
    hw := by decide
    g := ![![![-1515181, -433159, -1332955], ![12383705, 1460666, 0]], ![![-12156654267, -825747349, -9869822734], ![98237815873, 11751697741, 0]]]
    h := ![![![-3853174, 84714, -117], ![-19757334, 14345, 0]], ![![-2988140, 65745, -97], ![-15321831, 11221, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N2 : Ideal.span {4} * I241N2 =  Ideal.span {B.equivFun.symm ![-20236, -1130, 493]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E241RS2 


noncomputable def E251RS1 : RelationCertificate Table 4 ![![251, 0, 0], ![-84, 1, 0]]
  ![3692, -205, -17] ![![4, 0, 0], ![-1, 1, 0]] where
    su := ![![1004, 0, 0], ![-336, 4, 0]]
    hsu := by decide
    w := ![![14768, -820, -68], ![-8452, 2808, -376]]
    hw := by decide
    g := ![![![341925, 117565, -245308], ![-56087, 521820, 0]], ![![-97709, -33597, 82846], ![16032, -174609, 0]]]
    h := ![![![93916, -1080, -1], ![280586, 117, 0]], ![![-53663, 709, -2], ![-160325, 204, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N1 : Ideal.span {4} * I251N1 =  Ideal.span {B.equivFun.symm ![3692, -205, -17]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E251RS1 


noncomputable def E251RS2 : RelationCertificate Table 4 ![![251, 0, 0], ![-67, 1, 0]]
  ![-11812, -1264, 395] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![1004, 0, 0], ![-268, 4, 0]]
    hsu := by decide
    w := ![![-47248, -5056, 1580], ![98788, 6200, -2528]]
    hw := by decide
    g := ![![![-1975889, -466532, -93299], ![-610601, 0, 0]], ![![430814, 101717, 20339], ![133133, 7, 0]]]
    h := ![![![-1480084, 22170, -1], ![-5544616, 323, 0]], ![![3095504, -46277, 0], ![11596221, -316, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R251N2 : Ideal.span {4} * I251N2 =  Ideal.span {B.equivFun.symm ![-11812, -1264, 395]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E251RS2 


noncomputable def E257RS1 : RelationCertificate Table 4 ![![257, 0, 0], ![12, 1, 0]]
  ![12, 1, 0] ![![4, 0, 0], ![-69, -3, 2]] where
    su := ![![1028, 0, 0], ![48, 4, 0]]
    hsu := by decide
    w := ![![48, 4, 0], ![-268, -4, 16]]
    hw := by decide
    g := ![![![27, -2, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![468, 39, 0], ![-10022, 0, 0]], ![![-2711, -239, -2], ![58055, 259, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R257N1 : Ideal.span {4} * I257N1 =  Ideal.span {B.equivFun.symm ![12, 1, 0]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E257RS1 
