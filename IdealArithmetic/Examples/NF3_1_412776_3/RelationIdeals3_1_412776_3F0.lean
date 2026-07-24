import IdealArithmetic.Examples.NF3_1_412776_3.PrimesBelow3_1_412776_3F0
import IdealArithmetic.Examples.NF3_1_412776_3.ClassGroupData3_1_412776_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![14, 1, 1]]
  ![4, -1, 0] ![![2, 0, 0], ![15, 1, 1]] where
    su := ![![4, 0, 0], ![28, 2, 2]]
    hsu := by decide
    w := ![![8, -2, 0], ![-52, 10, 2]]
    hw := by decide
    g := ![![![-5, 41, -21], ![25, 0, -3]], ![![1, 248, -127], ![159, 0, -18]]]
    h := ![![![2, -23, -9], ![24, -3, 0]], ![![-34, 91, 35], ![-93, 12, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![4, -1, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![15, 1, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![15, 1, 1]] where
    su := ![![2, 0, 0], ![15, 1, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![15, 1, 1]]
    hw := by decide
    g := ![![![-7, 27, -14], ![16, 0, -2]], ![![4, 193, -94], ![105, 0, -14]]]
    h := ![![![-7, 27, -14], ![16, 0, -2]], ![![4, 193, -94], ![105, 0, -14]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 242 ![![3, 0, 0], ![1, 1, 0]]
  ![2, -9, 2] ![![242, 0, 0], ![29, 1, 1]] where
    su := ![![726, 0, 0], ![242, 242, 0]]
    hsu := by decide
    w := ![![484, -2178, 484], ![-726, 0, 0]]
    hw := by decide
    g := ![![![19236754, 1384292, 338906], ![2312555, -42163920, 4]], ![![8896998, 640235, 156744], ![1069561, -19500813, 2]]]
    h := ![![![0, -4, 0], ![2, 1, 0]], ![![-1, -1, -2], ![0, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {242} * I3N0 =  Ideal.span {B.equivFun.symm ![2, -9, 2]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E3RS0 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![0, 1, 0]]
  ![-630, -43, -22] ![![2, 0, 0], ![15, 1, 1]] where
    su := ![![14, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![-1260, -86, -44], ![-16730, -1142, -584]]
    hw := by decide
    g := ![![![-5, -5, -2], ![3, 0, 0]], ![![-8, 4, -1], ![0, 0, 0]]]
    h := ![![![-90, -14, -4], ![55, 3, 0]], ![![-1195, -160, -40], ![549, -6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-630, -43, -22]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 121 ![![11, 0, 0], ![12, 1, 1]]
  ![123, -9, 2] ![![121, 0, 0], ![9, 1, 0]] where
    su := ![![1331, 0, 0], ![1452, 121, 121]]
    hsu := by decide
    w := ![![14883, -1089, 242], ![1331, 0, 0]]
    hw := by decide
    g := ![![![0, -4032, -896], ![1, 54208, 0]], ![![-4, -4424, -983], ![56, 59472, 0]]]
    h := ![![![-3, -2, -1], ![13, 0, 0]], ![![-11, -1, -1], ![11, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {121} * I11N0 =  Ideal.span {B.equivFun.symm ![123, -9, 2]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 1 ![![11, 0, 0], ![-2, 1, 0]]
  ![1, 0, 0] ![![11, 0, 0], ![-2, 1, 0]] where
    su := ![![11, 0, 0], ![-2, 1, 0]]
    hsu := by decide
    w := ![![11, 0, 0], ![-2, 1, 0]]
    hw := by decide
    g := ![![![17, -8, 0], ![88, 0, 0]], ![![-2, 3, -2], ![-10, 11, 0]]]
    h := ![![![17, -8, 0], ![88, 0, 0]], ![![-2, 3, -2], ![-10, 11, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {1} * I11N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 22 ![![13, 0, 0], ![3, 1, 0]]
  ![970, -295, 24] ![![22, 0, 0], ![7, 1, 1]] where
    su := ![![286, 0, 0], ![66, 22, 0]]
    hsu := by decide
    w := ![![21340, -6490, 528], ![-23562, 5940, 44]]
    hw := by decide
    g := ![![![-47525384980306, 7202559468580, -259787313585], ![-14806132850303, 10260726790945, -11420]], ![![-14257615510685, 2160767842658, -77936194204], ![-4441839860267, 3078218040428, -3426]]]
    h := ![![![43504, 15495, 696], ![-188194, -4512, 0]], ![![-48159, -17157, -768], ![208332, 4993, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {22} * I13N0 =  Ideal.span {B.equivFun.symm ![970, -295, 24]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 22 ![![13, 0, 0], ![5, 1, 0]]
  ![342, 23, 12] ![![22, 0, 0], ![7, 1, 1]] where
    su := ![![286, 0, 0], ![110, 22, 0]]
    hsu := by decide
    w := ![![7524, 506, 264], ![6314, 440, 220]]
    hw := by decide
    g := ![![![79112566, -11987118, 431618], ![24646935, -17079260, -1142]], ![![79112385, -11987091, 431617], ![24646881, -17079221, -1142]]]
    h := ![![![21944, 5318, 374], ![-56986, -2425, 0]], ![![18414, 4458, 312], ![-47819, -2023, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {22} * I13N1 =  Ideal.span {B.equivFun.symm ![342, 23, 12]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 22 ![![19, 0, 0], ![4, 1, 0]]
  ![34, 1, 1] ![![22, 0, 0], ![5, 2, 1]] where
    su := ![![418, 0, 0], ![88, 22, 0]]
    hsu := by decide
    w := ![![748, 22, 22], ![506, 66, 22]]
    hw := by decide
    g := ![![![437, -74, 12], ![95, -90, 0]], ![![162, -29, 4], ![48, -34, 0]]]
    h := ![![![30, 5, -1], ![-134, 10, 0]], ![![17, 2, -1], ![-75, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {22} * I19N1 =  Ideal.span {B.equivFun.symm ![34, 1, 1]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 121 ![![23, 0, 0], ![-10, 1, 0]]
  ![465525, 31773, 16252] ![![121, 0, 0], ![9, 1, 0]] where
    su := ![![2783, 0, 0], ![-1210, 121, 0]]
    hsu := by decide
    w := ![![56328525, 3844533, 1966492], ![6009949, 410190, 209814]]
    hw := by decide
    g := ![![![-28092, 45924894, 10206226], ![377543, -617476622, 0]], ![![10596, -17328261, -3850986], ![-142342, 232984636, 0]]]
    h := ![![![2147265, -233898, 5222], ![4892157, -51927, 0]], ![![229113, -24951, 556], ![521993, -5527, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {121} * I23N1 =  Ideal.span {B.equivFun.symm ![465525, 31773, 16252]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 242 ![![29, 0, 0], ![3, 1, 0]]
  ![47518, 3243, 1659] ![![242, 0, 0], ![-83, 2, 1]] where
    su := ![![7018, 0, 0], ![726, 242, 0]]
    hsu := by decide
    w := ![![11499356, 784806, 401478], ![-3209162, -219010, -112046]]
    hw := by decide
    g := ![![![-896109541, 929779570, -37161972], ![314874001, 2169580805, 0]], ![![-96800841, 100438027, -4014366], ![34013883, 234365676, 0]]]
    h := ![![![47312, 15507, 171], ![-441510, -1650, 0]], ![![-13211, -4332, -49], ![123286, 479, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {242} * I29N1 =  Ideal.span {B.equivFun.symm ![47518, 3243, 1659]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E29RS1 
