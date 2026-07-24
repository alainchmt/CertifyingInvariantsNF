import IdealArithmetic.Examples.NF3_1_542700_2.PrimesBelow3_1_542700_2F0
import IdealArithmetic.Examples.NF3_1_542700_2.ClassGroupData3_1_542700_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 11 ![![2, 0, 0], ![-20, -1, 1]]
  ![-38, -8, -3] ![![11, 0, 0], ![-5, 1, 0]] where
    su := ![![22, 0, 0], ![-220, -11, 11]]
    hsu := by decide
    w := ![![-418, -88, -33], ![-440, -88, -33]]
    hw := by decide
    g := ![![![6, -1, 0], ![10, 0, 0]], ![![-35, -579, 697], ![-24, -1276, 0]]]
    h := ![![![-134, 804, -22], ![1091, 0, -105]], ![![-135, 804, -22], ![1091, 0, -105]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {11} * I2N0 =  Ideal.span {B.equivFun.symm ![-38, -8, -3]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E2RS0 


noncomputable def E5RS0 : RelationCertificate Table 539 ![![5, 0, 0], ![0, 1, 0]]
  ![265, 28, -17] ![![539, 0, 0], ![105, 1, 0]] where
    su := ![![2695, 0, 0], ![0, 539, 0]]
    hsu := by decide
    w := ![![142835, 15092, -9163], ![24255, 2695, -1617]]
    hw := by decide
    g := ![![![-55, -8173, -467], ![282, 41952, 0]], ![![-18, -735, -42], ![92, 3772, 0]]]
    h := ![![![53, 10, -7], ![-22, 3, 0]], ![![9, 0, -3], ![5, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {539} * I5N0 =  Ideal.span {B.equivFun.symm ![265, 28, -17]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 49 ![![7, 0, 0], ![-23, 0, 1]]
  ![-131, -7, 6] ![![49, 0, 0], ![7, 1, 0]] where
    su := ![![343, 0, 0], ![-1127, 0, 49]]
    hsu := by decide
    w := ![![-6419, -343, 294], ![343, 0, 0]]
    hw := by decide
    g := ![![![0, -28, -24], ![1, 196, 0]], ![![-1, 92, 79], ![8, -645, 0]]]
    h := ![![![1, -1, 0], ![6, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {49} * I7N0 =  Ideal.span {B.equivFun.symm ![-131, -7, 6]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 1 ![![7, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![7, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {1} * I7N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 121 ![![11, 0, 0], ![-24, -1, 1]]
  ![601, -13, -9] ![![121, 0, 0], ![-49, 1, 0]] where
    su := ![![1331, 0, 0], ![-2904, -121, 121]]
    hsu := by decide
    w := ![![72721, -1573, -1089], ![-31339, 968, 363]]
    hw := by decide
    g := ![![![38, -2671, 327], ![93, -6594, 0]], ![![45, 5969, -731], ![111, 14742, 0]]]
    h := ![![![11, -3, 1], ![-20, 0, 0]], ![![7, 2, -1], ![14, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {121} * I11N0 =  Ideal.span {B.equivFun.symm ![601, -13, -9]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![-5, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![-5, 1, 0]] where
    su := ![![11, 0, 0], ![-5, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![-5, 1, 0]]
    hw := by decide
    g := ![![![56, -11, 0], ![121, 0, 0]], ![![-20, 9, -6], ![-43, 11, 0]]]
    h := ![![![56, -11, 0], ![121, 0, 0]], ![![-20, 9, -6], ![-43, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 539 ![![13, 0, 0], ![-25, -4, 1]]
  ![8089, 1652, 614] ![![539, 0, 0], ![105, 1, 0]] where
    su := ![![7007, 0, 0], ![-13475, -2156, 539]]
    hsu := by decide
    w := ![![4359971, 890428, 330946], ![978285, 199969, 74382]]
    hw := by decide
    g := ![![![-137340947174813, 394424888159611362, 22538639781064690], ![705016862164038, -2024721140332311316, 0]], ![![262909813164245, -755041928766026887, -43145396152514823], ![-1349603707576466, 3875894754367581605, 0]]]
    h := ![![![153, 52, 66], ![-244, 0, 0]], ![![30, 11, 15], ![-57, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {539} * I13N0 =  Ideal.span {B.equivFun.symm ![8089, 1652, 614]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 847 ![![13, 0, 0], ![-2, 1, 0]]
  ![-5413, -1106, -412] ![![847, 0, 0], ![-49, 1, 0]] where
    su := ![![11011, 0, 0], ![-1694, 847, 0]]
    hsu := by decide
    w := ![![-4584811, -936782, -348964], ![178717, 36421, 13552]]
    hw := by decide
    g := ![![![10, -16497, 2020], ![173, -285160, 0]], ![![26, 1927, -236], ![456, 33320, 0]]]
    h := ![![![-10386063, 5280439, -263134], ![-67506703, 570055, 0]], ![![404857, -205834, 10252], ![2631465, -22210, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {847} * I13N1 =  Ideal.span {B.equivFun.symm ![-5413, -1106, -412]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS1 


noncomputable def E23RS0 : RelationCertificate Table 5929 ![![23, 0, 0], ![1, 1, 0]]
  ![-12347, -2527, -949] ![![5929, 0, 0], ![-2590, 1, 0]] where
    su := ![![136367, 0, 0], ![5929, 5929, 0]]
    hsu := by decide
    w := ![![-73205363, -14982583, -5626621], ![31779440, 6504113, 2442748]]
    hw := by decide
    g := ![![![-449, -32472983, 75227], ![-1027, -74336802, 0]], ![![1377, -2782093, 6445], ![3152, -6368736, 0]]]
    h := ![![![-535, -535, -2603], ![-42, 9820, 0]], ![![232, 232, 1130], ![24, -4263, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {5929} * I23N0 =  Ideal.span {B.equivFun.symm ![-12347, -2527, -949]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 7 ![![23, 0, 0], ![10, 1, 0]]
  ![-443, -91, -34] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![161, 0, 0], ![70, 7, 0]]
    hsu := by decide
    w := ![![-3101, -637, -238], ![-7140, -1463, -546]]
    hw := by decide
    g := ![![![-1, -3, -244], ![0, 286, 0]], ![![10, 0, -110], ![1, 128, 0]]]
    h := ![![![-1071, -130, -14], ![2419, 48, 0]], ![![-2480, -307, -36], ![5602, 125, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {7} * I23N1 =  Ideal.span {B.equivFun.symm ![-443, -91, -34]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 11 ![![23, 0, 0], ![-11, 1, 0]]
  ![-13, -1, 1] ![![11, 0, 0], ![-5, 1, 0]] where
    su := ![![253, 0, 0], ![-121, 11, 0]]
    hsu := by decide
    w := ![![-143, -11, 11], ![275, 22, -11]]
    hw := by decide
    g := ![![![14, 227, -275], ![25, 504, 0]], ![![-3, -109, 131], ![-2, -240, 0]]]
    h := ![![![-1652, 185, -19], ![-3453, 73, 0]], ![![3204, -337, 25], ![6697, -96, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {11} * I23N2 =  Ideal.span {B.equivFun.symm ![-13, -1, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E23RS2 


noncomputable def E31RS1 : RelationCertificate Table 5929 ![![31, 0, 0], ![-2, 1, 0]]
  ![26009, 525, -800] ![![5929, 0, 0], ![-2590, 1, 0]] where
    su := ![![183799, 0, 0], ![-11858, 5929, 0]]
    hsu := by decide
    w := ![![154207361, 3112725, -4743200], ![-67531310, -1357741, 2075150]]
    hw := by decide
    g := ![![![-2768763421, -44750438154463, 103668971174], ![-6338223288, -102442221681866, 0]], ![![122614102, 1981746633587, -4590918952], ![280686878, 4536593077693, 0]]]
    h := ![![![327519239, -164375345, 1848460], ![5076535200, -9550510, 0]], ![![-143429014, 71984151, -809494], ![-2223144022, 4182444, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {5929} * I31N1 =  Ideal.span {B.equivFun.symm ![26009, 525, -800]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E31RS1 
