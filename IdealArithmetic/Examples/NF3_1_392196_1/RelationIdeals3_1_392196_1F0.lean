import IdealArithmetic.Examples.NF3_1_392196_1.PrimesBelow3_1_392196_1F0
import IdealArithmetic.Examples.NF3_1_392196_1.ClassGroupData3_1_392196_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 2 ![![2, 0, 0], ![14, 1, 1]]
  ![-30, 16, -9] ![![2, 0, 0], ![15, 0, 1]] where
    su := ![![4, 0, 0], ![28, 2, 2]]
    hsu := by decide
    w := ![![-60, 32, -18], ![416, -166, 56]]
    hw := by decide
    g := ![![![266, 139, -330], ![1902, -3, 0]], ![![2773, 1451, -3316], ![19185, -18, 0]]]
    h := ![![![-204, 932, 507], ![-648, 0, 75]], ![![860, -4150, -2263], ![2889, 0, -333]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {2} * I2N0 =  Ideal.span {B.equivFun.symm ![-30, 16, -9]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![15, 0, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![15, 0, 1]] where
    su := ![![2, 0, 0], ![15, 0, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![15, 0, 1]]
    hw := by decide
    g := ![![![-14, 0, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-14, 0, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E3RS0 : RelationCertificate Table 3 ![![3, 0, 0], ![14, 0, 1]]
  ![-157, 26, 24] ![![3, 0, 0], ![-14, -1, -1]] where
    su := ![![9, 0, 0], ![42, 0, 3]]
    hsu := by decide
    w := ![![-471, 78, 72], ![-2958, 801, 69]]
    hw := by decide
    g := ![![![2811, -3003, -1257], ![-11695, 0, -52]], ![![15904, -17285, -7296], ![-65983, 0, -234]]]
    h := ![![![-41, 78, 41], ![-151, 26, 0]], ![![-360, 801, 336], ![-1519, 267, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {3} * I3N0 =  Ideal.span {B.equivFun.symm ![-157, 26, 24]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0, 0], ![15, -1, 1]]
  ![1, 0, 0] ![![3, 0, 0], ![-14, -1, -1]] where
    su := ![![3, 0, 0], ![15, -1, 1]]
    hsu := by decide
    w := ![![3, 0, 0], ![-14, -1, -1]]
    hw := by decide
    g := ![![![43, -97, -53], ![-99, 0, 12]], ![![173, -505, -277], ![-522, 0, 62]]]
    h := ![![![-6, -51, 11], ![15, 0, 6]], ![![-7, 240, -54], ![-63, 0, -28]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 3 ![![7, 0, 0], ![0, 1, 0]]
  ![7, -2, 0] ![![3, 0, 0], ![-14, -1, -1]] where
    su := ![![21, 0, 0], ![0, 3, 0]]
    hsu := by decide
    w := ![![21, -6, 0], ![66, -27, 9]]
    hw := by decide
    g := ![![![515, -1517, -833], ![-1577, 0, 186]], ![![12, -1, 0], ![-4, 0, 0]]]
    h := ![![![-35, 35, -108], ![5, 126, 0]], ![![-110, 109, -339], ![20, 396, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3} * I7N0 =  Ideal.span {B.equivFun.symm ![7, -2, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS0 


noncomputable def E17RS0 : RelationCertificate Table 6 ![![17, 0, 0], ![0, 1, 0]]
  ![-13688, -142, -587] ![![6, 0, 0], ![13, 0, 1]] where
    su := ![![102, 0, 0], ![0, 6, 0]]
    hsu := by decide
    w := ![![-82128, -852, -3522], ![-216306, -2244, -9276]]
    hw := by decide
    g := ![![![1, -3, -7], ![11, 0, 0]], ![![-37, 25, 5], ![-62, 11, 0]]]
    h := ![![![150568, -150860, 454085], ![-8866, -1286672, 0]], ![![396561, -397329, 1195954], ![-23369, -3388794, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {6} * I17N0 =  Ideal.span {B.equivFun.symm ![-13688, -142, -587]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E17RS0 


noncomputable def E19RS1 : RelationCertificate Table 12 ![![19, 0, 0], ![-9, 1, 0]]
  ![-2, -2, 3] ![![12, 0, 0], ![69, 1, 5]] where
    su := ![![228, 0, 0], ![-108, 12, 0]]
    hsu := by decide
    w := ![![-24, -24, 36], ![-12, 108, -144]]
    hw := by decide
    g := ![![![-31698239, 115703458, 28765395], ![-160637269, 28546725, -36882]], ![![14088103, -51423770, -12784623], ![71394357, -12687436, 16392]]]
    h := ![![![35, -257, 141], ![-25, -446, 0]], ![![189, -1412, 774], ![-146, -2453, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {12} * I19N1 =  Ideal.span {B.equivFun.symm ![-2, -2, 3]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 2 ![![23, 0, 0], ![2, 1, 0]]
  ![-4, 2, -1] ![![2, 0, 0], ![15, 0, 1]] where
    su := ![![46, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![-8, 4, -2], ![54, -20, 6]]
    hw := by decide
    g := ![![![-4, 2, -5], ![27, 0, 0]], ![![-13, 11, 3], ![-8, 3, 0]]]
    h := ![![![-196, 0, -587], ![2, 2250, 0]], ![![1297, -6, 3921], ![128, -15030, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {2} * I23N0 =  Ideal.span {B.equivFun.symm ![-4, 2, -1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![-4, 1, 0]]
  ![284, -36, -57] ![![2, 0, 0], ![15, 0, 1]] where
    su := ![![46, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![568, -72, -114], ![-1242, -90, 554]]
    hw := by decide
    g := ![![![11500, 6027, -13719], ![79401, -69, 0]], ![![-296, -97, 348], ![-1962, 15, 0]]]
    h := ![![![1620, -5056, 5073], ![-484, -19456, 0]], ![![-3495, 10920, -10957], ![1083, 42048, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![284, -36, -57]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS1 


noncomputable def E29RS0 : RelationCertificate Table 6 ![![29, 0, 0], ![4, 1, 0]]
  ![-404, 100, 21] ![![6, 0, 0], ![17, 1, 1]] where
    su := ![![174, 0, 0], ![24, 6, 0]]
    hsu := by decide
    w := ![![-2424, 600, 126], ![3978, -1440, 354]]
    hw := by decide
    g := ![![![650280382, -773028655, 256207393], ![1756324259, -411694150, 493]], ![![67271415, -79968907, 26504155], ![181691560, -42589085, 51]]]
    h := ![![![-99908, -101678, -306831], ![-17278, 1483020, 0]], ![![164799, 167718, 506131], ![28518, -2446290, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {6} * I29N0 =  Ideal.span {B.equivFun.symm ![-404, 100, 21]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 6 ![![29, 0, 0], ![-8, 1, 0]]
  ![-224, 4, 75] ![![6, 0, 0], ![17, 1, 1]] where
    su := ![![174, 0, 0], ![-48, 6, 0]]
    hsu := by decide
    w := ![![-1344, 24, 450], ![5970, -1452, -342]]
    hw := by decide
    g := ![![![-6762339, 8030361, -2659198], ![-18264745, 4274556, 78]], ![![1819468, -2161610, 716040], ![4914250, -1150853, -21]]]
    h := ![![![-39920, 224812, -135273], ![18776, 653832, 0]], ![![179559, -1011107, 608403], ![-84379, -2940624, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {6} * I29N1 =  Ideal.span {B.equivFun.symm ![-224, 4, 75]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E29RS1 


noncomputable def E31RS0 : RelationCertificate Table 6 ![![31, 0, 0], ![11, 1, 0]]
  ![20, 0, 1] ![![6, 0, 0], ![13, 0, 1]] where
    su := ![![186, 0, 0], ![66, 6, 0]]
    hsu := by decide
    w := ![![120, 0, 6], ![306, 6, 12]]
    hw := by decide
    g := ![![![804, -511, -174], ![1727, -341, 0]], ![![260, -165, -56], ![557, -110, 0]]]
    h := ![![![-92, -492, -329], ![-48, 1700, 0]], ![![-244, -1254, -838], ![-95, 4330, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {6} * I31N0 =  Ideal.span {B.equivFun.symm ![20, 0, 1]} * (J0 ^ 1*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_2 E31RS0 


noncomputable def E31RS1 : RelationCertificate Table 4 ![![31, 0, 0], ![-6, 1, 0]]
  ![-18, 6, -1] ![![4, 0, 0], ![15, 0, 1]] where
    su := ![![124, 0, 0], ![-24, 4, 0]]
    hsu := by decide
    w := ![![-72, 24, -4], ![164, -48, 0]]
    hw := by decide
    g := ![![![8118, -10377, -4392], ![29375, -5928, 0]], ![![219921, -280110, -118725], ![795030, -160063, 0]]]
    h := ![![![654, -2768, 2081], ![-202, -10752, 0]], ![![-1467, 6255, -4704], ![515, 24304, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N1 : Ideal.span {4} * I31N1 =  Ideal.span {B.equivFun.symm ![-18, 6, -1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E31RS1 


noncomputable def E31RS2 : RelationCertificate Table 3 ![![31, 0, 0], ![-5, 1, 0]]
  ![-5, 1, 0] ![![3, 0, 0], ![-14, -1, -1]] where
    su := ![![93, 0, 0], ![-15, 3, 0]]
    hsu := by decide
    w := ![![-15, 3, 0], ![-12, 15, -3]]
    hw := by decide
    g := ![![![-73, 254, 140], ![267, 0, -31]], ![![29, -48, -26], ![-48, 0, 6]]]
    h := ![![![155, -559, 480], ![-30, -2480, 0]], ![![146, -523, 449], ![-22, -2320, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N2 : Ideal.span {3} * I31N2 =  Ideal.span {B.equivFun.symm ![-5, 1, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E31RS2 
