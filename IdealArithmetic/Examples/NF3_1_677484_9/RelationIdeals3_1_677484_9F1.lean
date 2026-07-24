import IdealArithmetic.Examples.NF3_1_677484_9.PrimesBelow3_1_677484_9F1
import IdealArithmetic.Examples.NF3_1_677484_9.ClassGroupData3_1_677484_9

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 121 ![![37, 0, 0], ![9, 1, 0]]
  ![1127, 43, -37] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![4477, 0, 0], ![1089, 121, 0]]
    hsu := by decide
    w := ![![136367, 5203, -4477], ![-42229, -1452, 1331]]
    hw := by decide
    g := ![![![5, -587, 121], ![36, -2445, 0]], ![![2, -335, 69], ![19, -1395, 0]]]
    h := ![![![724826, 87959, 4949], ![-2979715, -30525, 0]], ![![-224458, -27245, -1537], ![922733, 9480, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {121} * I37N1 =  Ideal.span {B.equivFun.symm ![1127, 43, -37]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E37RS1 


noncomputable def E41RS0 : RelationCertificate Table 11 ![![41, 0, 0], ![-20, 1, 0]]
  ![82373, 16213, 5573] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![451, 0, 0], ![-220, 11, 0]]
    hsu := by decide
    w := ![![906103, 178343, 61303], ![1767326, 347853, 119570]]
    hw := by decide
    g := ![![![-681, 168, 317], ![-226, -526, 0]], ![![498, -74, -152], ![175, 240, 0]]]
    h := ![![![18667993, -1103414, 51289], ![38265267, -349546, 0]], ![![36411306, -2152161, 100034], ![74635144, -681754, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N0 : Ideal.span {11} * I41N0 =  Ideal.span {B.equivFun.symm ![82373, 16213, 5573]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS0 


noncomputable def E41RS1 : RelationCertificate Table 11 ![![41, 0, 0], ![-1, 1, 0]]
  ![13963, -157, -221] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![451, 0, 0], ![-11, 11, 0]]
    hsu := by decide
    w := ![![153593, -1727, -2431], ![-1166, 5379, -1826]]
    hw := by decide
    g := ![![![-137191, -753236, -1104977], ![-118362, 2003436, 0]], ![![-63591, -10248, -2189], ![-24047, -4959, 0]]]
    h := ![![![698, -361, -7], ![14655, 11, 0]], ![![-4, 14, -8], ![-58, 27, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {11} * I41N1 =  Ideal.span {B.equivFun.symm ![13963, -157, -221]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 


noncomputable def E43RS0 : RelationCertificate Table 11 ![![43, 0, 0], ![0, 1, 0]]
  ![43, 9, 3] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![473, 0, 0], ![0, 11, 0]]
    hsu := by decide
    w := ![![473, 99, 33], ![946, 187, 66]]
    hw := by decide
    g := ![![![-13, -2, -3], ![-2, 6, 0]], ![![2, 0, 0], ![-1, 0, 0]]]
    h := ![![![1, 0, -3], ![9, 22, 0]], ![![2, 0, 0], ![17, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N0 : Ideal.span {11} * I43N0 =  Ideal.span {B.equivFun.symm ![43, 9, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E43RS0 


noncomputable def E43RS2 : RelationCertificate Table 121 ![![43, 0, 0], ![-1, 1, 0]]
  ![28717, 784, -835] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![5203, 0, 0], ![-121, 121, 0]]
    hsu := by decide
    w := ![![3474757, 94864, -101035], ![-1048223, -24079, 28919]]
    hw := by decide
    g := ![![![-1085390, -580771478, 120167659], ![-4539507, -2423377588, 0]], ![![38901, 20259661, -4191817], ![158174, 84536329, 0]]]
    h := ![![![1366, -680, -19], ![30021, -3, 0]], ![![-410, 205, -1], ![-8967, 47, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N2 : Ideal.span {121} * I43N2 =  Ideal.span {B.equivFun.symm ![28717, 784, -835]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS2 


noncomputable def E59RS1 : RelationCertificate Table 11 ![![59, 0, 0], ![27, 1, 0]]
  ![1757, 346, 119] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![649, 0, 0], ![297, 11, 0]]
    hsu := by decide
    w := ![![19327, 3806, 1309], ![37730, 7425, 2552]]
    hw := by decide
    g := ![![![-23979, 824243, 1245377], ![66218, -2283200, 0]], ![![-11413, 391514, 591555], ![31454, -1084520, 0]]]
    h := ![![![278230, 13491, 709], ![-607919, -6952, 0]], ![![543224, 26357, 1388], ![-1186918, -13610, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {11} * I59N1 =  Ideal.span {B.equivFun.symm ![1757, 346, 119]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 


noncomputable def E67RS1 : RelationCertificate Table 11 ![![67, 0, 0], ![-12, 1, 0]]
  ![7, 3, 1] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![737, 0, 0], ![-132, 11, 0]]
    hsu := by decide
    w := ![![77, 33, 11], ![286, 55, 22]]
    hw := by decide
    g := ![![![-9, 87, 131], ![5, -240, 0]], ![![-2, -9, -12], ![10, 22, 0]]]
    h := ![![![61, 5, -5], ![340, 56, 0]], ![![158, -5, -4], ![880, 45, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {11} * I67N1 =  Ideal.span {B.equivFun.symm ![7, 3, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E67RS1 


noncomputable def E71RS1 : RelationCertificate Table 121 ![![71, 0, 0], ![-19, 1, 0]]
  ![-397511, -78240, -26894] ![![121, 0, 0], ![-29, 1, 0]] where
    su := ![![8591, 0, 0], ![-2299, 121, 0]]
    hsu := by decide
    w := ![![-48098831, -9467040, -3254174], ![4589167, 903265, 310486]]
    hw := by decide
    g := ![![![-3047392, -1626927814, 336627496], ![-12715203, -6788654481, 0]], ![![812851, 433947061, -89787950], ![3391594, 1810723642, 0]]]
    h := ![![![-2226714, 121452, -2164], ![-8299957, 21125, 0]], ![![212484, -11588, 206], ![792023, -2010, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R71N1 : Ideal.span {121} * I71N1 =  Ideal.span {B.equivFun.symm ![-397511, -78240, -26894]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E71RS1 


noncomputable def E73RS1 : RelationCertificate Table 11 ![![73, 0, 0], ![-6, 1, 0]]
  ![25, 6, 2] ![![11, 0, 0], ![4, 1, 0]] where
    su := ![![803, 0, 0], ![-66, 11, 0]]
    hsu := by decide
    w := ![![275, 66, 22], ![616, 121, 44]]
    hw := by decide
    g := ![![![-14723, 503761, 761158], ![40455, -1395456, 0]], ![![1022, -35073, -52992], ![-2806, 97152, 0]]]
    h := ![![![1675, -275, -4], ![20375, 49, 0]], ![![3740, -627, 4], ![45494, -48, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R73N1 : Ideal.span {11} * I73N1 =  Ideal.span {B.equivFun.symm ![25, 6, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E73RS1 
