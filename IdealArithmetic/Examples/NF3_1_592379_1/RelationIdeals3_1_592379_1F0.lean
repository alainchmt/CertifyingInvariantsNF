import IdealArithmetic.Examples.NF3_1_592379_1.PrimesBelow3_1_592379_1F0
import IdealArithmetic.Examples.NF3_1_592379_1.ClassGroupData3_1_592379_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 8 ![![2, 0, 0], ![33, 1, 1]]
  ![-51, -1, -1] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![16, 0, 0], ![264, 8, 8]]
    hsu := by decide
    w := ![![-408, -8, -8], ![16, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![1, 0, 0]], ![![3, -2, 0], ![7, 0, 0]]]
    h := ![![![-9, 0, 0], ![-1, 0, 0]], ![![-32, -1, -1], ![2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {8} * I2N1 =  Ideal.span {B.equivFun.symm ![-51, -1, -1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E2RS1 


noncomputable def E7RS0 : RelationCertificate Table 28 ![![7, 0, 0], ![34, -3, 1]]
  ![55, -3, 1] ![![28, 0, 0], ![2, 1, 0]] where
    su := ![![196, 0, 0], ![952, -84, 28]]
    hsu := by decide
    w := ![![1540, -84, 28], ![196, 0, 0]]
    hw := by decide
    g := ![![![166, -65737, -32910], ![-2323, 921480, 0]], ![![807, -317727, -159065], ![-11287, 4453820, 0]]]
    h := ![![![-31, 3, -1], ![8, 0, 0]], ![![-33, 3, -1], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {28} * I7N0 =  Ideal.span {B.equivFun.symm ![55, -3, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 16 ![![7, 0, 0], ![2, 1, 0]]
  ![-51, -1, -1] ![![112, 0, 0], ![30, 1, 0]] where
    su := ![![112, 0, 0], ![32, 16, 0]]
    hsu := by decide
    w := ![![-5712, -112, -112], ![-1616, -32, -32]]
    hw := by decide
    g := ![![![-2, 0, 0], ![7, 0, 0]], ![![-22, -1, 0], ![82, 1, 0]]]
    h := ![![![-7885, -4330, -207], ![27419, 1442, 0]], ![![-2233, -1227, -59], ![7765, 411, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {16} * I7N1 =  Ideal.span {B.equivFun.symm ![-51, -1, -1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 112 ![![13, 0, 0], ![27, -6, 1]]
  ![11009, 155, 219] ![![112, 0, 0], ![30, 1, 0]] where
    su := ![![1456, 0, 0], ![3024, -672, 112]]
    hsu := by decide
    w := ![![1233008, 17360, 24528], ![349104, 4928, 6944]]
    hw := by decide
    g := ![![![-18, 120, 4], ![67, -450, 0]], ![![-5, 389, 13], ![22, -1455, 0]]]
    h := ![![![176, 161, -8], ![323, 0, 0]], ![![30, 50, -3], ![101, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {112} * I13N0 =  Ideal.span {B.equivFun.symm ![11009, 155, 219]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 28 ![![13, 0, 0], ![5, 1, 0]]
  ![-1, -3, 1] ![![28, 0, 0], ![2, 1, 0]] where
    su := ![![364, 0, 0], ![140, 28, 0]]
    hsu := by decide
    w := ![![-28, -84, 28], ![84, -56, 0]]
    hw := by decide
    g := ![![![-4, -52, -26], ![3, 726, 0]], ![![-2, -26, -13], ![1, 363, 0]]]
    h := ![![![-112, -28, -1], ![291, 14, 0]], ![![226, 55, 2], ![-587, -26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {28} * I13N1 =  Ideal.span {B.equivFun.symm ![-1, -3, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 8 ![![17, 0, 0], ![8, 1, 0]]
  ![5, -1, -1] ![![8, 0, 0], ![-2, 1, 0]] where
    su := ![![136, 0, 0], ![64, 8, 0]]
    hsu := by decide
    w := ![![40, -8, -8], ![-96, 56, 0]]
    hw := by decide
    g := ![![![43, 13, -5], ![-5, 47, 0]], ![![24, 8, -3], ![-5, 28, 0]]]
    h := ![![![85, 11, 0], ![-180, -1, 0]], ![![-236, -53, -3], ![500, 51, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {8} * I17N1 =  Ideal.span {B.equivFun.symm ![5, -1, -1]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 112 ![![19, 0, 0], ![-7, 1, 0]]
  ![-141, 81, 1] ![![112, 0, 0], ![30, 1, 0]] where
    su := ![![2128, 0, 0], ![-784, 112, 0]]
    hsu := by decide
    w := ![![-15792, 9072, 112], ![-4144, 2240, 112]]
    hw := by decide
    g := ![![![-253354, 113540518, 3784966], ![945957, -423916131, 0]], ![![90969, -40782683, -1359524], ![-339646, 152266671, 0]]]
    h := ![![![-142299, 22208, -268], ![-386220, 5093, 0]], ![![-37295, 5826, -71], ![-101224, 1350, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {112} * I19N1 =  Ideal.span {B.equivFun.symm ![-141, 81, 1]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E19RS1 


noncomputable def E29RS0 : RelationCertificate Table 2 ![![29, 0, 0], ![14, 1, 0]]
  ![351, 5, 7] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![58, 0, 0], ![28, 2, 0]]
    hsu := by decide
    w := ![![702, 10, 14], ![602, 8, 12]]
    hw := by decide
    g := ![![![-2, -1, 3106], ![1, -6210, 0]], ![![2, -2, 1553], ![0, -3105, 0]]]
    h := ![![![2563, 305, 9], ![-5284, -254, 0]], ![![2205, 266, 8], ![-4546, -226, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {2} * I29N0 =  Ideal.span {B.equivFun.symm ![351, 5, 7]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 56 ![![29, 0, 0], ![-8, 1, 0]]
  ![2663, 37, 53] ![![56, 0, 0], ![-26, 1, 0]] where
    su := ![![1624, 0, 0], ![-448, 56, 0]]
    hsu := by decide
    w := ![![149128, 2072, 2968], ![-64680, -896, -1288]]
    hw := by decide
    g := ![![![415980, 60987618, -2346293], ![895959, 131392405, 0]], ![![-105357, -15447383, 594286], ![-226923, -33280014, 0]]]
    h := ![![![10731, -1394, 10], ![38567, -237, 0]], ![![-4647, 609, -5], ![-16701, 122, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {56} * I29N1 =  Ideal.span {B.equivFun.symm ![2663, 37, 53]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E29RS1 


noncomputable def E29RS2 : RelationCertificate Table 28 ![![29, 0, 0], ![-7, 1, 0]]
  ![107, -71, 5] ![![28, 0, 0], ![2, 1, 0]] where
    su := ![![812, 0, 0], ![-196, 28, 0]]
    hsu := by decide
    w := ![![2996, -1988, 140], ![644, -280, -56]]
    hw := by decide
    g := ![![![342, 50, 30], ![33, -648, 0]], ![![-64, -9, -5], ![17, 105, 0]]]
    h := ![![![22409, -3363, 23], ![92822, -662, 0]], ![![4811, -716, 4], ![19928, -118, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N2 : Ideal.span {28} * I29N2 =  Ideal.span {B.equivFun.symm ![107, -71, 5]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS2 


noncomputable def E31RS1 : RelationCertificate Table 14 ![![31, 0, 0], ![11, 1, 0]]
  ![755, 11, 15] ![![14, 0, 0], ![2, 1, 0]] where
    su := ![![434, 0, 0], ![154, 14, 0]]
    hsu := by decide
    w := ![![10570, 154, 210], ![2800, 42, 56]]
    hw := by decide
    g := ![![![-1785, 178633, 89764], ![12513, -1256697, 0]], ![![-699, 69900, 35125], ![4898, -491751, 0]]]
    h := ![![![73713, 7838, 104], ![-207668, -3209, 0]], ![![19524, 2070, 27], ![-55004, -833, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {14} * I31N1 =  Ideal.span {B.equivFun.symm ![755, 11, 15]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS1 
