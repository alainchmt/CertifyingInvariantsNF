import IdealArithmetic.Examples.NF3_1_614075_2.PrimesBelow3_1_614075_2F0
import IdealArithmetic.Examples.NF3_1_614075_2.ClassGroupData3_1_614075_2

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 32 ![![2, 0, 0], ![25, -1, 1]]
  ![65, 19, -3] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![64, 0, 0], ![800, -32, 32]]
    hsu := by decide
    w := ![![2080, 608, -96], ![1376, 480, -32]]
    hw := by decide
    g := ![![![1, 455, 29], ![35, -915, 0]], ![![175, 5683, 364], ![270, -11430, 0]]]
    h := ![![![-5, 11, -3], ![3, 0, 0]], ![![-16, 9, -2], ![3, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {32} * I2N0 =  Ideal.span {B.equivFun.symm ![65, 19, -3]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 16 ![![5, 0, 0], ![-2, 1, 0]]
  ![593, -45, 13] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![80, 0, 0], ![-32, 16, 0]]
    hsu := by decide
    w := ![![9488, -720, 208], ![-1456, 112, -32]]
    hw := by decide
    g := ![![![1, 0, 44734451], ![4, -715751217, 0]], ![![1, 0, -20876040], ![9, 334016641, 0]]]
    h := ![![![23709, -13035, 618], ![58976, -3077, 0]], ![![-3635, 1999, -95], ![-9042, 473, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {16} * I5N0 =  Ideal.span {B.equivFun.symm ![593, -45, 13]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E5RS0 


noncomputable def E7RS0 : RelationCertificate Table 4 ![![7, 0, 0], ![0, 1, 0]]
  ![-21, -11, -1] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![28, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![-84, -44, -4], ![112, 16, -12]]
    hw := by decide
    g := ![![![421, -31, 9], ![-4, 1, 0]], ![![-148, 10, -3], ![5, -1, 0]]]
    h := ![![![-3, -2, 0], ![3, -1, 0]], ![![4, 0, 0], ![4, -3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {4} * I7N0 =  Ideal.span {B.equivFun.symm ![-21, -11, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 4 ![![7, 0, 0], ![3, 1, 0]]
  ![403, 181, 7] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![28, 0, 0], ![12, 4, 0]]
    hsu := by decide
    w := ![![1612, 724, 28], ![-784, 144, 188]]
    hw := by decide
    g := ![![![93933, -6722, 1985], ![-1680, 315, 0]], ![![7237, -518, 129], ![-129, 120, 0]]]
    h := ![![![2449, 1045, 75], ![-5580, -518, 0]], ![![-1054, -450, -31], ![2394, 264, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {4} * I7N1 =  Ideal.span {B.equivFun.symm ![403, 181, 7]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 4 ![![11, 0, 0], ![-4, 1, 0]]
  ![1775, -135, 39] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![44, 0, 0], ![-16, 4, 0]]
    hsu := by decide
    w := ![![7100, -540, 156], ![-4368, 332, -96]]
    hw := by decide
    g := ![![![1, 2, 4], ![1, -13, 0]], ![![-8, -4, -1], ![3, 4, 0]]]
    h := ![![![2969, -768, 17], ![7721, -148, 0]], ![![-1820, 473, -11], ![-4732, 97, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {4} * I11N0 =  Ideal.span {B.equivFun.symm ![1775, -135, 39]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E13RS0 : RelationCertificate Table 2 ![![13, 0, 0], ![30, -3, 1]]
  ![43, -3, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![26, 0, 0], ![60, -6, 2]]
    hsu := by decide
    w := ![![86, -6, 2], ![-112, 6, -2]]
    hw := by decide
    g := ![![![-1, -1, 357], ![1, -714, 0]], ![![2, 0, 816], ![1, -1632, 0]]]
    h := ![![![-29, 3, -1], ![14, 0, 0]], ![![-2, 0, 0], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {2} * I13N0 =  Ideal.span {B.equivFun.symm ![43, -3, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 32 ![![13, 0, 0], ![2, 1, 0]]
  ![-233, -107, -5] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![416, 0, 0], ![64, 32, 0]]
    hsu := by decide
    w := ![![-7456, -3424, -160], ![-3168, -1760, -192]]
    hw := by decide
    g := ![![![-131683, 10566874, 660960], ![264410, -21150353, 0]], ![![-10177, 812861, 50843], ![20317, -1626989, 0]]]
    h := ![![![-12505, -6421, -85], ![81166, 1100, 0]], ![![-5327, -2737, -37], ![34576, 475, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {32} * I13N1 =  Ideal.span {B.equivFun.symm ![-233, -107, -5]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E13RS1 


noncomputable def E19RS0 : RelationCertificate Table 32 ![![19, 0, 0], ![8, 1, 0]]
  ![64223, -4883, 1411] ![![32, 0, 0], ![16, 1, 0]] where
    su := ![![608, 0, 0], ![256, 32, 0]]
    hsu := by decide
    w := ![![2055136, -156256, 45152], ![869536, -66112, 19104]]
    hw := by decide
    g := ![![![46, -3905, -245], ![-83, 7815, 0]], ![![27, -1767, -111], ![-41, 3540, 0]]]
    h := ![![![8883005, 1414926, 38228], ![-21089109, -724921, 0]], ![![3758431, 598657, 16174], ![-8922877, -306709, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N0 : Ideal.span {32} * I19N0 =  Ideal.span {B.equivFun.symm ![64223, -4883, 1411]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E19RS0 


noncomputable def E19RS2 : RelationCertificate Table 2 ![![19, 0, 0], ![-2, 1, 0]]
  ![-71, -51, -9] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![38, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-142, -102, -18], ![1008, 262, -60]]
    hw := by decide
    g := ![![![61651, -3750, 2592], ![-1875, -2475, 0]], ![![-14474, 880, -393], ![441, 150, 0]]]
    h := ![![![-239, 118, -2], ![-2235, 29, 0]], ![![1712, -843, 2], ![16012, -68, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N2 : Ideal.span {2} * I19N2 =  Ideal.span {B.equivFun.symm ![-71, -51, -9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS2 


noncomputable def E29RS0 : RelationCertificate Table 16 ![![29, 0, 0], ![4, 1, 0]]
  ![149, 63, 1] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![464, 0, 0], ![64, 16, 0]]
    hsu := by decide
    w := ![![2384, 1008, 16], ![-112, 112, 64]]
    hw := by decide
    g := ![![![697, -53, -346662], ![0, 5546837, 0]], ![![37, -3, -43832], ![3, 701325, 0]]]
    h := ![![![7501, 1916, 10], ![-54345, -289, 0]], ![![-351, -92, -1], ![2543, 33, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N0 : Ideal.span {16} * I29N0 =  Ideal.span {B.equivFun.symm ![149, 63, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E29RS0 


noncomputable def E29RS1 : RelationCertificate Table 16 ![![29, 0, 0], ![12, 1, 0]]
  ![-11, -1, 1] ![![16, 0, 0], ![0, 1, 0]] where
    su := ![![464, 0, 0], ![192, 16, 0]]
    hsu := by decide
    w := ![![-176, -16, 16], ![-112, -48, 0]]
    hw := by decide
    g := ![![![-9, 0, 8994381], ![10, -143910099, 0]], ![![-3, 0, 3411374], ![3, -54581985, 0]]]
    h := ![![![-1231, -139, -3], ![2974, 88, 0]], ![![-803, -91, -2], ![1940, 58, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {16} * I29N1 =  Ideal.span {B.equivFun.symm ![-11, -1, 1]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E29RS1 
