import IdealArithmetic.Examples.NF3_1_203987_1.PrimesBelow3_1_203987_1F1
import IdealArithmetic.Examples.NF3_1_203987_1.ClassGroupData3_1_203987_1

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![-13, 1, 0]]
  ![-1129, -189, -131] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![74, 0, 0], ![-26, 2, 0]]
    hsu := by decide
    w := ![![-2258, -378, -262], ![-11528, -1930, -1338]]
    hw := by decide
    g := ![![![23, 2140, -6628], ![1071, 2646, 0]], ![![-39, -600, 1845], ![-299, -735, 0]]]
    h := ![![![-23284, 2037, -88], ![-66183, 625, 0]], ![![-118876, 10348, -432], ![-337896, 3063, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![-1129, -189, -131]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E47RS1 : RelationCertificate Table 2 ![![47, 0, 0], ![21, 1, 0]]
  ![7, 1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![94, 0, 0], ![42, 2, 0]]
    hsu := by decide
    w := ![![14, 2, 2], ![88, 14, 8]]
    hw := by decide
    g := ![![![13, -8526, 26646], ![-4261, -10659, 0]], ![![3, -4039, 12622], ![-2018, -5049, 0]]]
    h := ![![![14, -7, -2], ![-31, 19, 0]], ![![160, -4, -3], ![-356, 29, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R47N1 : Ideal.span {2} * I47N1 =  Ideal.span {B.equivFun.symm ![7, 1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E47RS1 


noncomputable def E67RS1 : RelationCertificate Table 4 ![![67, 0, 0], ![5, 1, 0]]
  ![289827, 48519, 33635] ![![4, 0, 0], ![0, 1, 0]] where
    su := ![![268, 0, 0], ![20, 4, 0]]
    hsu := by decide
    w := ![![1159308, 194076, 134540], ![2959880, 495504, 343500]]
    hw := by decide
    g := ![![![2001, -1731615216662, 4599602918940], ![-432903804164, -3679682335179, 0]], ![![105, -103380013759, 274603161585], ![-25845003439, -219682529278, 0]]]
    h := ![![![398526, 79791, 880], ![-5282283, -5065, 0]], ![![1017500, 203724, 2255], ![-13486506, -13042, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N1 : Ideal.span {4} * I67N1 =  Ideal.span {B.equivFun.symm ![289827, 48519, 33635]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS1 


noncomputable def E79RS1 : RelationCertificate Table 2 ![![79, 0, 0], ![4, 1, 0]]
  ![153, 7, -9] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![158, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![306, 14, -18], ![-792, 58, 8]]
    hw := by decide
    g := ![![![-1245, 7141, -22982], ![3571, 9135, 0]], ![![-224, 474, -1601], ![237, 630, 0]]]
    h := ![![![143, 35, -1], ![-2786, 14, 0]], ![![-380, -95, -4], ![7406, 64, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R79N1 : Ideal.span {2} * I79N1 =  Ideal.span {B.equivFun.symm ![153, 7, -9]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E79RS1 
