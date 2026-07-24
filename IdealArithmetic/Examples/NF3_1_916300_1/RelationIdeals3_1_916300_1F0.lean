import IdealArithmetic.Examples.NF3_1_916300_1.PrimesBelow3_1_916300_1F0
import IdealArithmetic.Examples.NF3_1_916300_1.ClassGroupData3_1_916300_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 9 ![![2, 0, 0], ![1, 1, 0]]
  ![1787, 65, 34] ![![9, 0, 0], ![0, 1, 0]] where
    su := ![![18, 0, 0], ![9, 9, 0]]
    hsu := by decide
    w := ![![16083, 585, 306], ![5202, 189, 99]]
    hw := by decide
    g := ![![![1, -1, 3], ![3, -26, 0]], ![![9, -3, 2], ![5, -20, 0]]]
    h := ![![![1190, 469, 157], ![-593, -280, 0]], ![![384, 151, 51], ![-190, -91, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {9} * I2N0 =  Ideal.span {B.equivFun.symm ![1787, 65, 34]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0], ![32, -1, 1]]
  ![-60131, -2186, -1144] ![![9, 0, 0], ![0, 1, 0]] where
    su := ![![27, 0, 0], ![288, -9, 9]]
    hsu := by decide
    w := ![![-541179, -19674, -10296], ![-175032, -6363, -3330]]
    hw := by decide
    g := ![![![7, -2, -859633956], ![8, 7736705600, 0]], ![![18, -20, -9241064991], ![5, 83169584960, 0]]]
    h := ![![![-225, -1348, 238], ![-1858, 0, 0]], ![![-104, -435, 76], ![-598, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![-60131, -2186, -1144]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E3RS1 


noncomputable def E5RS0 : RelationCertificate Table 11 ![![5, 0, 0], ![-2, 1, 0]]
  ![-52, -2, -1] ![![11, 0, 0], ![26, -4, 1]] where
    su := ![![55, 0, 0], ![-22, 11, 0]]
    hsu := by decide
    w := ![![-572, -22, -11], ![-1199, -44, -22]]
    hw := by decide
    g := ![![![-24, 4, -1], ![10, 0, 0]], ![![-5, 1, 0], ![1, 0, 0]]]
    h := ![![![-1396, 766, -37], ![-3464, 184, 0]], ![![-2931, 1609, -78], ![-7273, 388, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {11} * I5N0 =  Ideal.span {B.equivFun.symm ![-52, -2, -1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 99 ![![7, 0, 0], ![2, 1, 0]]
  ![127, -32, -4] ![![99, 0, 0], ![-18, 7, 1]] where
    su := ![![693, 0, 0], ![198, 99, 0]]
    hsu := by decide
    w := ![![12573, -3168, -396], ![-12078, 3861, 99]]
    hw := by decide
    g := ![![![-5, -63, 3], ![75, -80, 0]], ![![-44, -27, 0], ![52, -30, 0]]]
    h := ![![![17165, 9496, 463], ![-60014, -3245, 0]], ![![-16374, -9065, -446], ![57248, 3123, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {99} * I7N0 =  Ideal.span {B.equivFun.symm ![127, -32, -4]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 11 ![![11, 0, 0], ![3, 1, 0]]
  ![-632, -23, -12] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![121, 0, 0], ![33, 11, 0]]
    hsu := by decide
    w := ![![-6952, -253, -132], ![-572, -22, -11]]
    hw := by decide
    g := ![![![-1, 38, -19], ![9, 210, 0]], ![![2, 13, -7], ![8, 78, 0]]]
    h := ![![![-616, -206, -7], ![2048, 65, 0]], ![![-56, -20, -1], ![188, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {11} * I11N0 =  Ideal.span {B.equivFun.symm ![-632, -23, -12]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![11, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![17, -8, 0], ![88, 0, 0]], ![![-2, 3, -1], ![-10, 11, 0]]]
    h := ![![![17, -8, 0], ![88, 0, 0]], ![![-2, 3, -1], ![-10, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 33 ![![13, 0, 0], ![28, 4, 1]]
  ![-524, 148, 11] ![![33, 0, 0], ![15, 7, 1]] where
    su := ![![429, 0, 0], ![924, 132, 33]]
    hsu := by decide
    w := ![![-17292, 4884, 363], ![28248, -10857, 396]]
    hw := by decide
    g := ![![![1289, -101, 16], ![593, -28, 0]], ![![4634, -301, 53], ![2051, -60, 0]]]
    h := ![![![-36, 12, 1], ![-2, 0, 0]], ![![12, -33, -1], ![25, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {33} * I13N0 =  Ideal.span {B.equivFun.symm ![-524, 148, 11]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 99 ![![13, 0, 0], ![-5, 1, 0]]
  ![-38, 10, -1] ![![99, 0, 0], ![9, 1, 0]] where
    su := ![![1287, 0, 0], ![-495, 99, 0]]
    hsu := by decide
    w := ![![-3762, 990, -99], ![-495, 99, 0]]
    hw := by decide
    g := ![![![-1, 0, 0], ![5, -1, 0]], ![![0, -18, -2], ![1, 198, 0]]]
    h := ![![![-23796, 5244, -97], ![-61862, 1260, 0]], ![![-3115, 688, -13], ![-8098, 169, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {99} * I13N1 =  Ideal.span {B.equivFun.symm ![-38, 10, -1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E13RS1 


noncomputable def E17RS0 : RelationCertificate Table 3 ![![17, 0, 0], ![0, 1, 0]]
  ![-19448, -707, -370] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![51, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![-58344, -2121, -1110], ![-56610, -2058, -1077]]
    hw := by decide
    g := ![![![53, -23, -3], ![-6, 16, 0]], ![![21, -3, -4], ![-1, 8, 0]]]
    h := ![![![-1144, -42, 0], ![7, -370, 0]], ![![-1110, -41, 0], ![11, -359, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {3} * I17N0 =  Ideal.span {B.equivFun.symm ![-19448, -707, -370]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 3 ![![17, 0, 0], ![8, 1, 0]]
  ![-142, 107, -20] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![51, 0, 0], ![24, 3, 0]]
    hsu := by decide
    w := ![![-426, 321, -60], ![-3060, 798, 87]]
    hw := by decide
    g := ![![![147577, 4828, 2149], ![1611, 1976, 0]], ![![94717, 3099, 1346], ![1033, 1368, 0]]]
    h := ![![![-958, -191, -11], ![2018, 167, 0]], ![![-7340, -1436, -66], ![15470, 1151, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {3} * I17N1 =  Ideal.span {B.equivFun.symm ![-142, 107, -20]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 11 ![![19, 0, 0], ![7, 1, 0]]
  ![5, -2, 0] ![![11, 0, 0], ![26, -4, 1]] where
    su := ![![209, 0, 0], ![77, 11, 0]]
    hsu := by decide
    w := ![![55, -22, 0], ![-176, 22, 11]]
    hw := by decide
    g := ![![![-9, -2, 0], ![-4, 0, 0]], ![![-5, -1, 0], ![-2, 0, 0]]]
    h := ![![![218, 31, 0], ![-591, 0, 0]], ![![-748, -128, -3], ![2028, 58, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {11} * I19N1 =  Ideal.span {B.equivFun.symm ![5, -2, 0]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 33 ![![23, 0, 0], ![7, 1, 0]]
  ![-256451, -9323, -4879] ![![33, 0, 0], ![9, 1, 0]] where
    su := ![![759, 0, 0], ![231, 33, 0]]
    hsu := by decide
    w := ![![-8462883, -307659, -161007], ![-3054546, -111045, -58113]]
    hw := by decide
    g := ![![![-22, -1227, -136], ![-8, 4520, 0]], ![![-5, -430, -47], ![15, 1570, 0]]]
    h := ![![![-601723, -94173, -1555], ![1940454, 30886, 0]], ![![-217186, -33996, -562], ![700388, 11165, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {33} * I23N1 =  Ideal.span {B.equivFun.symm ![-256451, -9323, -4879]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS1 


noncomputable def E31RS1 : RelationCertificate Table 11 ![![31, 0, 0], ![14, 1, 0]]
  ![23, -2, -2] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![341, 0, 0], ![154, 11, 0]]
    hsu := by decide
    w := ![![253, -22, -22], ![-352, 121, 0]]
    hw := by decide
    g := ![![![2483, 148775, -74978], ![13077, 824780, 0]], ![![1182, 70330, -35444], ![6185, 389896, 0]]]
    h := ![![![1753, 154, 2], ![-3880, -64, 0]], ![![-2428, -243, -5], ![5374, 155, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {11} * I31N1 =  Ideal.span {B.equivFun.symm ![23, -2, -2]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS1 
