import IdealArithmetic.Examples.NF3_1_588735_1.PrimesBelow3_1_588735_1F0
import IdealArithmetic.Examples.NF3_1_588735_1.ClassGroupData3_1_588735_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 605 ![![3, 0, 0], ![0, 1, 0]]
  ![-46, 16, 5] ![![605, 0, 0], ![-138, 1, 0]] where
    su := ![![1815, 0, 0], ![0, 605, 0]]
    hsu := by decide
    w := ![![-27830, 9680, 3025], ![6655, -2420, -605]]
    hw := by decide
    g := ![![![41600732, -3123493611, 112356758], ![-14651389, -13595167527, 7]], ![![23779104, -1785394095, 64223308], ![-8374508, -7771020159, 4]]]
    h := ![![![-14, -50058, 5], ![150188, -2, 0]], ![![1, 11970, -7], ![-35910, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {605} * I3N0 =  Ideal.span {B.equivFun.symm ![-46, 16, 5]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E3RS0 


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![2, 1, 0]]
  ![1, 0, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![5, 0, 0], ![2, 1, 0]]
    hsu := by decide
    w := ![![5, 0, 0], ![2, 1, 0]]
    hw := by decide
    g := ![![![-1, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-1, -1, 0], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![-21, 1, -1]]
  ![-1, 1, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![25, 0, 0], ![-105, 5, -5]]
    hsu := by decide
    w := ![![-5, 5, 0], ![0, 0, 5]]
    hw := by decide
    g := ![![![-40, 0, -1], ![60, 0, 2]], ![![-69, 0, -2], ![59, 0, 2]]]
    h := ![![![8, 2, 3], ![7, -2, 0]], ![![4, 2, 3], ![6, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![-1, 1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 275 ![![7, 0, 0], ![0, 1, 0]]
  ![326, -1, 10] ![![275, 0, 0], ![27, 1, 0]] where
    su := ![![1925, 0, 0], ![0, 275, 0]]
    hsu := by decide
    w := ![![89650, -275, 2750], ![9350, 0, 275]]
    hw := by decide
    g := ![![![542164019917, 7148965593473, 1374856519263], ![79226887864, -75617106727246, -327182]], ![![31892021697, 420527658688, 80873964984], ![4660408316, -4448067966342, -19246]]]
    h := ![![![-178974, 87719, -447550], ![12538, 626572, 0]], ![![-18666, 9148, -46677], ![1312, 65348, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {275} * I7N0 =  Ideal.span {B.equivFun.symm ![326, -1, 10]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 121 ![![11, 0, 0], ![15, 1, 1]]
  ![-31, -5, 6] ![![121, 0, 0], ![-17, 1, 0]] where
    su := ![![1331, 0, 0], ![1815, 121, 121]]
    hsu := by decide
    w := ![![-3751, -605, 726], ![847, -121, -121]]
    hw := by decide
    g := ![![![-989216, 9172828, -2548501], ![214844, 61673724, 0]], ![![-1353394, 12549770, -3486722], ![293925, 84378672, 0]]]
    h := ![![![-11, -1, 0], ![6, 0, 0]], ![![-13, -1, -1], ![10, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {121} * I11N0 =  Ideal.span {B.equivFun.symm ![-31, -5, 6]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![5, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![5, 1, 0]] where
    su := ![![11, 0, 0], ![5, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![5, 1, 0]]
    hw := by decide
    g := ![![![92, 245, 315], ![77, -693, 0]], ![![41, 109, 140], ![34, -308, 0]]]
    h := ![![![92, 245, 315], ![77, -693, 0]], ![![41, 109, 140], ![34, -308, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E13RS1 : RelationCertificate Table 3025 ![![13, 0, 0], ![3, 1, 0]]
  ![76491, 409, 2510] ![![3025, 0, 0], ![-1348, 1, 0]] where
    su := ![![39325, 0, 0], ![9075, 3025, 0]]
    hsu := by decide
    w := ![![231385275, 1237225, 7592750], ![-102971000, -550550, -3378925]]
    hw := by decide
    g := ![![![-3931418664988, 3528961125842221, -13079915204041], ![2918516856283, 7913350870235528, 8061584]], ![![-1246547381399, 1118938893552405, -4147290186620], ![925383393841, 2509111251521672, 2556112]]]
    h := ![![![400594, 413862, 1058670], ![124283, -2752040, 0]], ![![-178273, -184177, -471129], ![-55305, 1224712, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {3025} * I13N1 =  Ideal.span {B.equivFun.symm ![76491, 409, 2510]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E13RS1 


noncomputable def E13RS2 : RelationCertificate Table 55 ![![13, 0, 0], ![-3, 1, 0]]
  ![4, 1, -10] ![![55, 0, 0], ![27, 1, 0]] where
    su := ![![715, 0, 0], ![-165, 55, 0]]
    hsu := by decide
    w := ![![220, 55, -550], ![-440, 330, -275]]
    hw := by decide
    g := ![![![-423, -7756, -1466], ![-321, 16367, -45]], ![![80, 1725, 326], ![92, -3641, 10]]]
    h := ![![![-1508, 3249, -4120], ![604, 10710, 0]], ![![3826, -8232, 10435], ![-1506, -27132, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N2 : Ideal.span {55} * I13N2 =  Ideal.span {B.equivFun.symm ![4, 1, -10]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS2 


noncomputable def E19RS1 : RelationCertificate Table 121 ![![19, 0, 0], ![3, 1, 0]]
  ![-1205, -7, -40] ![![121, 0, 0], ![-17, 1, 0]] where
    su := ![![2299, 0, 0], ![363, 121, 0]]
    hsu := by decide
    w := ![![-145805, -847, -4840], ![18271, 121, 605]]
    hw := by decide
    g := ![![![5058998, -46910856, 13033315], ![-1098452, -315406224, 0]], ![![1079616, -10010959, 2781360], ![-234369, -67308912, 0]]]
    h := ![![![-3660356, -3741860, -9456610], ![-774887, 35935110, 0]], ![![458653, 468867, 1184945], ![97108, -4502790, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {121} * I19N1 =  Ideal.span {B.equivFun.symm ![-1205, -7, -40]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 5 ![![23, 0, 0], ![2, 1, 0]]
  ![11, -6, 0] ![![5, 0, 0], ![2, 1, 0]] where
    su := ![![115, 0, 0], ![10, 5, 0]]
    hsu := by decide
    w := ![![55, -30, 0], ![10, 5, -30]]
    hw := by decide
    g := ![![![-9863, 6598, -600], ![-2624, 0, 1012]], ![![-884, 598, -54], ![-229, 0, 92]]]
    h := ![![![-1, -1, 0], ![17, 0, 0]], ![![54, 27, 138], ![16, -636, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {5} * I23N1 =  Ideal.span {B.equivFun.symm ![11, -6, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 3025 ![![29, 0, 0], ![14, 1, 0]]
  ![1862, -937, -255] ![![3025, 0, 0], ![-1348, 1, 0]] where
    su := ![![87725, 0, 0], ![42350, 3025, 0]]
    hsu := by decide
    w := ![![5632550, -2834425, -771375], ![-2525875, 1273525, 338800]]
    hw := by decide
    g := ![![![1807920749796540255393, -1622844775844486760209027, 6014993400746828210162], ![-1342122957543875378346, -3639071007451838393396475, -27194688]], ![![874800362803918667957, -785247472182045221102650, 2910480677777865827858], ![-649414334294785975390, -1760840810055612370812995, -13158720]]]
    h := ![![![30706, 274609, 105945], ![24318, -614532, 0]], ![![-13775, -123151, -47512], ![-10896, 275592, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {3025} * I29N0 =  Ideal.span {B.equivFun.symm ![1862, -937, -255]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 55 ![![29, 0, 0], ![-12, 1, 0]]
  ![3203, 17, 105] ![![55, 0, 0], ![27, 1, 0]] where
    su := ![![1595, 0, 0], ![-660, 55, 0]]
    hsu := by decide
    w := ![![176165, 935, 5775], ![92290, 495, 3025]]
    hw := by decide
    g := ![![![148337, 2702738, 520282], ![122025, -5722208, -160]], ![![-55639, -1013544, -195109], ![-45737, 2145864, 60]]]
    h := ![![![3252091, -27201392, 10492365], ![-2283663, -60855696, 0]], ![![1703714, -14250304, 5496755], ![-1196359, -31881168, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {55} * I29N1 =  Ideal.span {B.equivFun.symm ![3203, 17, 105]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS1 


noncomputable def E31RS1 : RelationCertificate Table 11 ![![31, 0, 0], ![9, 1, 0]]
  ![26, 1, 1] ![![11, 0, 0], ![5, 1, 0]] where
    su := ![![341, 0, 0], ![99, 11, 0]]
    hsu := by decide
    w := ![![286, 11, 11], ![187, 0, 11]]
    hw := by decide
    g := ![![![42, 113, 146], ![39, -321, 0]], ![![14, 35, 45], ![10, -99, 0]]]
    h := ![![![-3487, -15646, -9809], ![-1501, 60816, 0]], ![![-2296, -10287, -6449], ![-975, 39984, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {11} * I31N1 =  Ideal.span {B.equivFun.symm ![26, 1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS1 
