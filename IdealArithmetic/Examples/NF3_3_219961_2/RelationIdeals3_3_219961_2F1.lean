import IdealArithmetic.Examples.NF3_3_219961_2.PrimesBelow3_3_219961_2F1
import IdealArithmetic.Examples.NF3_3_219961_2.ClassGroupData3_3_219961_2

set_option linter.all false

noncomputable section


noncomputable def E37RS0 : RelationCertificate Table 2 ![![37, 0, 0], ![10, 1, 0]]
  ![-244, -7, 7] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![74, 0, 0], ![20, 2, 0]]
    hsu := by decide
    w := ![![-488, -14, 14], ![3706, 146, -118]]
    hw := by decide
    g := ![![![-215, -2009, -588], ![3549, 588, 0]], ![![-168, -1510, -442], ![2662, 441, 0]]]
    h := ![![![-2532, -289, -13], ![9344, 122, 0]], ![![19139, 2160, 89], ![-70629, -838, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N0 : Ideal.span {2} * I37N0 =  Ideal.span {B.equivFun.symm ![-244, -7, 7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS0 


noncomputable def E37RS1 : RelationCertificate Table 2 ![![37, 0, 0], ![-7, 1, 0]]
  ![-1452, -53, 45] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![74, 0, 0], ![-14, 2, 0]]
    hsu := by decide
    w := ![![-2904, -106, 90], ![19694, 718, -610]]
    hw := by decide
    g := ![![![-787, -7150, -2106], ![12451, 2058, 0]], ![![77, 514, 150], ![-889, -147, 0]]]
    h := ![![![-7740, 1117, -11], ![-40704, 113, 0]], ![![52527, -7563, 63], ![276236, -659, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {2} * I37N1 =  Ideal.span {B.equivFun.symm ![-1452, -53, 45]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E37RS2 : RelationCertificate Table 2 ![![37, 0, 0], ![-4, 1, 0]]
  ![-36, -1, 1] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![74, 0, 0], ![-8, 2, 0]]
    hsu := by decide
    w := ![![-72, -2, 2], ![558, 22, -18]]
    hw := by decide
    g := ![![![-677, -6131, -1808], ![10671, 1764, 0]], ![![70, 511, 150], ![-888, -147, 0]]]
    h := ![![![-260, 67, -3], ![-2396, 28, 0]], ![![2047, -512, 3], ![18865, -30, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N2 : Ideal.span {2} * I37N2 =  Ideal.span {B.equivFun.symm ![-36, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS2 


noncomputable def E61RS0 : RelationCertificate Table 2 ![![61, 0, 0], ![-25, 1, 0]]
  ![56, 19, 5] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![122, 0, 0], ![-50, 2, 0]]
    hsu := by decide
    w := ![![112, 38, 10], ![538, 186, 50]]
    hw := by decide
    g := ![![![9198, 82763, 24405], ![-144113, -23814, 0]], ![![-3654, -32936, -9713], ![57357, 9477, 0]]]
    h := ![![![796, -13, -3], ![1940, 47, 0]], ![![3779, -153, 1], ![9210, -9, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N0 : Ideal.span {2} * I61N0 =  Ideal.span {B.equivFun.symm ![56, 19, 5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS0 


noncomputable def E61RS1 : RelationCertificate Table 2 ![![61, 0, 0], ![-23, 1, 0]]
  ![-12, -1, 1] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![122, 0, 0], ![-46, 2, 0]]
    hsu := by decide
    w := ![![-24, -2, 2], ![-42, -2, 6]]
    hw := by decide
    g := ![![![5085, 45606, 13442], ![-79361, -13122, 0]], ![![-1775, -16046, -4730], ![27923, 4617, 0]]]
    h := ![![![-56, 19, -3], ![-148, 46, 0]], ![![-167, 13, -1], ![-442, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N1 : Ideal.span {2} * I61N1 =  Ideal.span {B.equivFun.symm ![-12, -1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS1 


noncomputable def E61RS2 : RelationCertificate Table 2 ![![61, 0, 0], ![-14, 1, 0]]
  ![4, 3, 1] ![![2, 0, 0], ![-25, -1, 1]] where
    su := ![![122, 0, 0], ![-28, 2, 0]]
    hsu := by decide
    w := ![![8, 6, 2], ![166, 34, 6]]
    hw := by decide
    g := ![![![389, 3384, 994], ![-5881, -972, 0]], ![![105, 843, 249], ![-1468, -243, 0]]]
    h := ![![![124, 1, -3], ![540, 46, 0]], ![![2265, -158, -1], ![9863, 16, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R61N2 : Ideal.span {2} * I61N2 =  Ideal.span {B.equivFun.symm ![4, 3, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E61RS2 


noncomputable def E67RS0 : RelationCertificate Table 4 ![![67, 0, 0], ![22, 1, 0]]
  ![-13918, -507, 431] ![![4, 0, 0], ![-25, -1, 1]] where
    su := ![![268, 0, 0], ![88, 4, 0]]
    hsu := by decide
    w := ![![-55672, -2028, 1724], ![188996, 6896, -5856]]
    hw := by decide
    g := ![![![-125, -406, -135], ![975, 152, 0]], ![![-45, -169, -59], ![354, 53, 0]]]
    h := ![![![-573246, -31859, -1003], ![1745162, 16908, 0]], ![![1946025, 108079, 3392], ![-5924383, -57182, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R67N0 : Ideal.span {4} * I67N0 =  Ideal.span {B.equivFun.symm ![-13918, -507, 431]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E67RS0 
