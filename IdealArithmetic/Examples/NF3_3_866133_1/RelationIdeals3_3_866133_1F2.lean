import IdealArithmetic.Examples.NF3_3_866133_1.PrimesBelow3_3_866133_1F2
import IdealArithmetic.Examples.NF3_3_866133_1.ClassGroupData3_3_866133_1

set_option linter.all false

noncomputable section


noncomputable def E97RS1 : RelationCertificate Table 16 ![![97, 0, 0], ![31, 1, 0]]
  ![2717, 99, -52] ![![16, 0, 0], ![6, 1, 0]] where
    su := ![![1552, 0, 0], ![496, 16, 0]]
    hsu := by decide
    w := ![![43472, 1584, -832], ![-1648, -64, 32]]
    hw := by decide
    g := ![![![1108, 7284, 6072], ![877, -24420, 74]], ![![358, 2363, 1970], ![283, -7923, 24]]]
    h := ![![![5257422, 91406098, 12191084], ![2622593, -295633800, 0]], ![![-199322, -3465041, -462142], ![-99347, 11206944, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {16} * I97N1 =  Ideal.span {B.equivFun.symm ![2717, 99, -52]} * (J0 ^ 4) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_4 E97RS1 


noncomputable def E103RS1 : RelationCertificate Table 4 ![![103, 0, 0], ![-1, 1, 0]]
  ![-1, 1, 0] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![412, 0, 0], ![-4, 4, 0]]
    hsu := by decide
    w := ![![-4, 4, 0], ![0, 0, 4]]
    hw := by decide
    g := ![![![40, 0, 1], ![63, 0, -1]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![0, 0, -1], ![52, 26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {4} * I103N1 =  Ideal.span {B.equivFun.symm ![-1, 1, 0]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E103RS1 


noncomputable def E113RS1 : RelationCertificate Table 4 ![![113, 0, 0], ![20, 1, 0]]
  ![75, 17, 4] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![452, 0, 0], ![80, 4, 0]]
    hsu := by decide
    w := ![![300, 68, 16], ![1580, 344, 80]]
    hw := by decide
    g := ![![![23219, 2253, 251], ![12177, 0, -336]], ![![4144, 402, 45], ![2173, 0, -60]]]
    h := ![![![-9309, -92414, -19460], ![-2375, 549746, 0]], ![![-48987, -486970, -102544], ![-12891, 2896873, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {4} * I113N1 =  Ideal.span {B.equivFun.symm ![75, 17, 4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E113RS1 


noncomputable def E131RS1 : RelationCertificate Table 32 ![![131, 0, 0], ![-37, 1, 0]]
  ![-63, -17, -4] ![![32, 0, 0], ![-10, 1, 0]] where
    su := ![![4192, 0, 0], ![-1184, 32, 0]]
    hsu := by decide
    w := ![![-2016, -544, -128], ![-800, -128, -32]]
    hw := by decide
    g := ![![![-423793, 2682958, -978170], ![216298, 7825830, 209]], ![![113561, -718892, 262098], ![-57934, -2096910, -56]]]
    h := ![![![163752, -3501904, 368680], ![-72891, -12074271, 0]], ![![65164, -1392983, 146653], ![-28899, -4802886, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R131N1 : Ideal.span {32} * I131N1 =  Ideal.span {B.equivFun.symm ![-63, -17, -4]} * (J0 ^ 5) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_5 E131RS1 
