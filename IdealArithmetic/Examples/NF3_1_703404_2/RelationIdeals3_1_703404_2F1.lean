import IdealArithmetic.Examples.NF3_1_703404_2.PrimesBelow3_1_703404_2F1
import IdealArithmetic.Examples.NF3_1_703404_2.ClassGroupData3_1_703404_2

set_option linter.all false

noncomputable section


noncomputable def E41RS0 : RelationCertificate Table 2 ![![41, 0, 0], ![6, 1, 0]]
  ![6, 1, 0] ![![2, 0, 0], ![-44, -4, 1]] where
    su := ![![82, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![12, 2, 0], ![-2, -2, 2]]
    hw := by decide
    g := ![![![7, -1, 0], ![1, 0, 0]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![-6, -1, 0], ![42, 0, 0]], ![![1, -6, -1], ![-7, 42, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {2} * I41N0 =  Ideal.span {B.equivFun.symm ![6, 1, 0]} * (J0 ^ 0*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_2 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 49 ![![41, 0, 0], ![8, 1, 0]]
  ![1051, 171, -29] ![![49, 0, 0], ![-11, 1, 0]] where
    su := ![![2009, 0, 0], ![392, 49, 0]]
    hsu := by decide
    w := ![![51499, 8379, -1421], ![-19159, -2744, 490]]
    hw := by decide
    g := ![![![50, -1042, 98], ![11, -4716, 0]], ![![27, -260, 25], ![29, -1188, 0]]]
    h := ![![![276019, 36381, 234], ![-1414466, -9623, 0]], ![![-102671, -13540, -88], ![526140, 3618, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {49} * I41N1 =  Ideal.span {B.equivFun.symm ![1051, 171, -29]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E41RS1 


noncomputable def E41RS2 : RelationCertificate Table 14 ![![41, 0, 0], ![-14, 1, 0]]
  ![-240, -62, 9] ![![14, 0, 0], ![-4, 1, 0]] where
    su := ![![574, 0, 0], ![-196, 14, 0]]
    hsu := by decide
    w := ![![-3360, -868, 126], ![3318, 602, -98]]
    hw := by decide
    g := ![![![233838, 12397680, -3114052], ![818751, 43596681, 0]], ![![-85571, -4535736, 1139284], ![-299532, -15949971, 0]]]
    h := ![![![-376, 28, 0], ![-1084, 9, 0]], ![![407, -16, -1], ![1175, 34, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N2 : Ideal.span {14} * I41N2 =  Ideal.span {B.equivFun.symm ![-240, -62, 9]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E41RS2 


noncomputable def E43RS1 : RelationCertificate Table 98 ![![43, 0, 0], ![10, 1, 0]]
  ![116, 33, 3] ![![98, 0, 0], ![-28, -4, 1]] where
    su := ![![4214, 0, 0], ![980, 98, 0]]
    hsu := by decide
    w := ![![11368, 3234, 294], ![2254, 784, 98]]
    hw := by decide
    g := ![![![965596642, 140223935, -13095989], ![-281741795, -391287180, 0]], ![![234902419, 34112527, -3185885], ![-68539766, -95189124, 0]]]
    h := ![![![292, 29, 0], ![-1244, 3, 0]], ![![51, 5, 0], ![-217, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {98} * I43N1 =  Ideal.span {B.equivFun.symm ![116, 33, 3]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E43RS1 


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![-23, 1, 0]]
  ![16, 8, -1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![94, 0, 0], ![-46, 2, 0]]
    hsu := by decide
    w := ![![32, 16, -2], ![-262, -50, 8]]
    hw := by decide
    g := ![![![93, 26, 74], ![15, -141, 0]], ![![-26, -8, -37], ![-3, 72, 0]]]
    h := ![![![752, -33, 0], ![1536, -1, 0]], ![![-6065, 334, -3], ![-12388, 145, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![16, 8, -1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E47RS1 


noncomputable def E53RS1 : RelationCertificate Table 98 ![![53, 0, 0], ![-24, 1, 0]]
  ![178, 16, -3] ![![98, 0, 0], ![38, 1, 0]] where
    su := ![![5194, 0, 0], ![-2352, 98, 0]]
    hsu := by decide
    w := ![![17444, 1568, -294], ![5978, 588, -98]]
    hw := by decide
    g := ![![![-7, -1445, -38], ![17, 3726, 0]], ![![4924, -1436802, -37814], ![-12698, 3705771, 0]]]
    h := ![![![482426, -23054, 123], ![1065350, -6522, 0]], ![![165329, -7897, 42], ![365099, -2227, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {98} * I53N1 =  Ideal.span {B.equivFun.symm ![178, 16, -3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E53RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![21, 1, 0]]
  ![-298, -106, -11] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![42, 2, 0]]
    hsu := by decide
    w := ![![-596, -212, -22], ![-2882, -1024, -106]]
    hw := by decide
    g := ![![![-377, -23, 7], ![-11, 0, 0]], ![![-77, -6, 0], ![-1, 3, 0]]]
    h := ![![![-6820, -365, -2], ![25642, 147, 0]], ![![-32896, -1747, -9], ![123683, 658, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![-298, -106, -11]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E79RS1 
