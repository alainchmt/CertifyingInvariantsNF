import IdealArithmetic.Examples.NF3_1_746956_1.PrimesBelow3_1_746956_1F4
import IdealArithmetic.Examples.NF3_1_746956_1.ClassGroupData3_1_746956_1

set_option linter.all false

noncomputable section


noncomputable def E197RS1 : RelationCertificate Table 99 ![![197, 0, 0], ![-73, 1, 0]]
  ![-1057, -36, -44] ![![99, 0, 0], ![-41, 1, 0]] where
    su := ![![19503, 0, 0], ![-7227, 99, 0]]
    hsu := by decide
    w := ![![-104643, -3564, -4356], ![38709, 1287, 1584]]
    hw := by decide
    g := ![![![-110993522776, -4166302200749, 1238618720716], ![3883153899, -11147568503380, -4140]], ![![39813099665, 1494442203216, -444289444390], ![-1392877595, 3998605005585, 1485]]]
    h := ![![![17632821, 1224764026, -195251980], ![-316694, 3496785456, 0]], ![![-6522581, -453060567, 72226952], ![117400, -1293519048, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {99} * I197N1 =  Ideal.span {B.equivFun.symm ![-1057, -36, -44]} * (J0 ^ 2*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_1 E197RS1 


noncomputable def E233RS1 : RelationCertificate Table 9 ![![233, 0, 0], ![36, 1, 0]]
  ![-40, 9, 1] ![![9, 0, 0], ![4, 1, 0]] where
    su := ![![2097, 0, 0], ![324, 9, 0]]
    hsu := by decide
    w := ![![-360, 81, 9], ![-63, 9, 99]]
    hw := by decide
    g := ![![![-2880376, 19709281, 27239251], ![909754, -22286651, 0]], ![![-465836, 3187529, 4405332], ![147140, -3604361, 0]]]
    h := ![![![44263, -1765975, -485644], ![-736, 10286823, 0]], ![![7727, -308840, -84931], ![-39, 1798994, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R233N1 : Ideal.span {9} * I233N1 =  Ideal.span {B.equivFun.symm ![-40, 9, 1]} * (J0 ^ 2*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_0 E233RS1 


noncomputable def E239RS1 : RelationCertificate Table 27 ![![239, 0, 0], ![13, 1, 0]]
  ![46, -9, -7] ![![27, 0, 0], ![13, 1, 0]] where
    su := ![![6453, 0, 0], ![351, 27, 0]]
    hsu := by decide
    w := ![![1242, -243, -189], ![-135, 54, -162]]
    hw := by decide
    g := ![![![1117, -17277, -11180], ![-84, 27448, 0]], ![![61, -1053, -681], ![11, 1672, 0]]]
    h := ![![![-113603, 1929416, 1248451], ![1979, -27125436, 0]], ![![12375, -210184, -136002], ![-206, 2954952, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R239N1 : Ideal.span {27} * I239N1 =  Ideal.span {B.equivFun.symm ![46, -9, -7]} * (J0 ^ 3*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_0 E239RS1 


noncomputable def E241RS0 : RelationCertificate Table 3 ![![241, 0, 0], ![85, 1, 0]]
  ![-89, -3, -4] ![![3, 0, 0], ![1, 1, 0]] where
    su := ![![723, 0, 0], ![255, 3, 0]]
    hsu := by decide
    w := ![![-267, -9, -12], ![-510, -12, -21]]
    hw := by decide
    g := ![![![309, -1026, -2429], ![-239, 662, 0]], ![![109, -366, -866], ![-84, 236, 0]]]
    h := ![![![-53727, 4755299, 587734], ![840, -12876718, 0]], ![![-102646, 9083568, 1122689], ![1652, -24597096, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N0 : Ideal.span {3} * I241N0 =  Ideal.span {B.equivFun.symm ![-89, -3, -4]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E241RS0 


noncomputable def E241RS1 : RelationCertificate Table 297 ![![241, 0, 0], ![-79, 1, 0]]
  ![-7996, -261, -341] ![![297, 0, 0], ![-41, 1, 0]] where
    su := ![![71577, 0, 0], ![-23463, 297, 0]]
    hsu := by decide
    w := ![![-2374812, -77517, -101277], ![291951, 9504, 12474]]
    hw := by decide
    g := ![![![-166505078588, -6185722207279, 1838812325958], ![2158202342, -49652245662041, -1054254955]], ![![54216739584, 2014170935314, -598746956028], ![-702745291, 16167572149927, 343282420]]]
    h := ![![![-143901619, -10845913054, 1590732594], ![2167378, -34851505045, 0]], ![![17690805, 1333360168, -195559329], ![-266381, 4284527121, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N1 : Ideal.span {297} * I241N1 =  Ideal.span {B.equivFun.symm ![-7996, -261, -341]} * (J0 ^ 3*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_3J1_1 E241RS1 


noncomputable def E241RS2 : RelationCertificate Table 1089 ![![241, 0, 0], ![-6, 1, 0]]
  ![3587, 135, 154] ![![1089, 0, 0], ![157, 1, 0]] where
    su := ![![262449, 0, 0], ![-6534, 1089, 0]]
    hsu := by decide
    w := ![![3906243, 147015, 167706], ![579348, 21780, 25047]]
    hw := by decide
    g := ![![![-195983, 31523188, 2153829], ![1633, -213222142, -498]], ![![1126, -190501, -13016], ![395, 1288542, 3]]]
    h := ![![![-156026927, -312193551, 1717005444], ![2589226, -37618028350, 0]], ![![-23140896, -46302522, 254655103], ![384222, -5579261800, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R241N2 : Ideal.span {1089} * I241N2 =  Ideal.span {B.equivFun.symm ![3587, 135, 154]} * (J0 ^ 2*J1^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2J1_2 E241RS2 
