import IdealArithmetic.Examples.NF3_1_190291_3.PrimesBelow3_1_190291_3F0
import IdealArithmetic.Examples.NF3_1_190291_3.ClassGroupData3_1_190291_3

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 32 ![![2, 0, 0], ![-49, -5, 1]]
  ![65, 3, -1] ![![32, 0, 0], ![3, 1, 0]] where
    su := ![![64, 0, 0], ![-1568, -160, 32]]
    hsu := by decide
    w := ![![2080, 96, -32], ![-64, 0, 0]]
    hw := by decide
    g := ![![![-3, -1, 0], ![31, 0, 0]], ![![26, -10152, -3387], ![-296, 108385, 0]]]
    h := ![![![8, -1, 0], ![-1, 0, 0]], ![![48, 5, -1], ![2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {32} * I2N0 =  Ideal.span {B.equivFun.symm ![65, 3, -1]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E2RS0 


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


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0, 0], ![-49, -4, 1]]
  ![58, 4, -1] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![27, 0, 0], ![-441, -36, 9]]
    hsu := by decide
    w := ![![522, 36, -9], ![-27, 0, 0]]
    hw := by decide
    g := ![![![-80, 1892, 478], ![179, -4302, 0]], ![![1283, -31227, -7887], ![-2892, 70983, 0]]]
    h := ![![![3, 0, 0], ![-1, 0, 0]], ![![48, 4, -1], ![3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![58, 4, -1]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![3, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![3, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 144 ![![7, 0, 0], ![0, 1, 0]]
  ![-343, -37, 7] ![![144, 0, 0], ![67, 1, 0]] where
    su := ![![1008, 0, 0], ![0, 144, 0]]
    hsu := by decide
    w := ![![-49392, -5328, 1008], ![-21168, -2304, 432]]
    hw := by decide
    g := ![![![-1103, 395418, 5902], ![2371, -849889, 0]], ![![3, 0, 0], ![-7, 0, 0]]]
    h := ![![![-49, -6, 0], ![5, 7, 0]], ![![-21, -3, 0], ![5, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {144} * I7N0 =  Ideal.span {B.equivFun.symm ![-343, -37, 7]} * (J0 ^ 4*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4J1_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 24 ![![7, 0, 0], ![2, 1, 0]]
  ![1, -5, -1] ![![24, 0, 0], ![-5, 1, 0]] where
    su := ![![168, 0, 0], ![48, 24, 0]]
    hsu := by decide
    w := ![![24, -120, -24], ![-264, -48, 0]]
    hw := by decide
    g := ![![![-844, -101247, 20283], ![-4033, -486790, 0]], ![![-108, -13388, 2682], ![-528, -64369, 0]]]
    h := ![![![13, 6, 0], ![-45, -1, 0]], ![![-375, -207, -10], ![1307, 70, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {24} * I7N1 =  Ideal.span {B.equivFun.symm ![1, -5, -1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 32 ![![7, 0, 0], ![-2, 1, 0]]
  ![-33, -3, 1] ![![32, 0, 0], ![3, 1, 0]] where
    su := ![![224, 0, 0], ![-64, 32, 0]]
    hsu := by decide
    w := ![![-1056, -96, 32], ![160, 32, 0]]
    hw := by decide
    g := ![![![-3776, 1300504, 433921], ![40296, -13885473, 0]], ![![1628, -562146, -187563], ![-17383, 6002017, 0]]]
    h := ![![![-2533, 1342, -39], ![-8849, 274, 0]], ![![385, -202, 5], ![1345, -35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {32} * I7N2 =  Ideal.span {B.equivFun.symm ![-33, -3, 1]} * (J0 ^ 5*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_0 E7RS2 


noncomputable def E17RS1 : RelationCertificate Table 72 ![![17, 0, 0], ![2, 1, 0]]
  ![23, 5, 1] ![![72, 0, 0], ![-5, 1, 0]] where
    su := ![![1224, 0, 0], ![144, 72, 0]]
    hsu := by decide
    w := ![![1656, 360, 72], ![144, 72, 0]]
    hw := by decide
    g := ![![![3321, 3456626, -691458], ![47805, 49784975, 0]], ![![425, 440490, -88115], ![6121, 6344280, 0]]]
    h := ![![![2895, 1469, 11], ![-24596, -186, 0]], ![![250, 125, 0], ![-2124, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {72} * I17N1 =  Ideal.span {B.equivFun.symm ![23, 5, 1]} * (J0 ^ 3*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_2 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 18 ![![19, 0, 0], ![-2, 1, 0]]
  ![5, 5, 1] ![![18, 0, 0], ![-5, 1, 0]] where
    su := ![![342, 0, 0], ![-36, 18, 0]]
    hsu := by decide
    w := ![![90, 90, 18], ![234, 54, 0]]
    hw := by decide
    g := ![![![559, 38060, -7634], ![1978, 137409, 0]], ![![-88, -6018, 1207], ![-305, -21725, 0]]]
    h := ![![![193, -96, 0], ![1831, 1, 0]], ![![501, -252, 1], ![4753, -19, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {18} * I19N1 =  Ideal.span {B.equivFun.symm ![5, 5, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 36 ![![23, 0, 0], ![9, 1, 0]]
  ![-13, 5, 1] ![![36, 0, 0], ![-5, 1, 0]] where
    su := ![![828, 0, 0], ![324, 36, 0]]
    hsu := by decide
    w := ![![-468, 180, 36], ![324, 36, 0]]
    hw := by decide
    g := ![![![576, 150785, -30180], ![4144, 1086479, 0]], ![![200, 52430, -10494], ![1441, 377784, 0]]]
    h := ![![![-1934, -278, -7], ![4941, 162, 0]], ![![1368, 188, 4], ![-3495, -92, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {36} * I23N1 =  Ideal.span {B.equivFun.symm ![-13, 5, 1]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E23RS1 


noncomputable def E31RS0 : RelationCertificate Table 288 ![![31, 0, 0], ![1, 1, 0]]
  ![-1271, -101, 23] ![![288, 0, 0], ![67, 1, 0]] where
    su := ![![8928, 0, 0], ![288, 288, 0]]
    hsu := by decide
    w := ![![-366048, -29088, 6624], ![-79200, -6336, 1440]]
    hw := by decide
    g := ![![![-1619448, 2113248624, 31541385], ![6961211, -9083918879, 0]], ![![-167352, 218323166, 3258592], ![719364, -938474495, 0]]]
    h := ![![![-41, -41, -37], ![0, 1170, 0]], ![![-9, -9, -8], ![4, 253, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {288} * I31N0 =  Ideal.span {B.equivFun.symm ![-1271, -101, 23]} * (J0 ^ 5*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5J1_2 E31RS0 


noncomputable def E31RS2 : RelationCertificate Table 6 ![![31, 0, 0], ![-7, 1, 0]]
  ![-31, -7, 1] ![![6, 0, 0], ![1, 1, 0]] where
    su := ![![186, 0, 0], ![-42, 6, 0]]
    hsu := by decide
    w := ![![-186, -42, 6], ![228, 36, -6]]
    hw := by decide
    g := ![![![1152, -42681, -43833], ![-6918, 262997, 0]], ![![-299, 11013, 11311], ![1787, -67866, 0]]]
    h := ![![![-78, 18, -1], ![-341, 32, 0]], ![![106, -15, 0], ![464, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {6} * I31N2 =  Ideal.span {B.equivFun.symm ![-31, -7, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E31RS2 
