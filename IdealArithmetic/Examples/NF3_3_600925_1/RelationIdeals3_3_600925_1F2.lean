import IdealArithmetic.Examples.NF3_3_600925_1.PrimesBelow3_3_600925_1F2
import IdealArithmetic.Examples.NF3_3_600925_1.ClassGroupData3_3_600925_1

set_option linter.all false

noncomputable section


noncomputable def E83RS1 : RelationCertificate Table 3 ![![83, 0, 0], ![-1, 1, 0]]
  ![-75923, -27935, -7142] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![249, 0, 0], ![-3, 3, 0]]
    hsu := by decide
    w := ![![-227769, -83805, -21426], ![-758088, -278931, -71313]]
    hw := by decide
    g := ![![![-49, -1211, 36], ![1453, 206, 0]], ![![17, 74, -13], ![-47, 0, 0]]]
    h := ![![![-10844, 9594, -88], ![-824129, 54, 0]], ![![-36094, 31933, -292], ![-2743106, 155, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R83N1 : Ideal.span {3} * I83N1 =  Ideal.span {B.equivFun.symm ![-75923, -27935, -7142]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E83RS1 


noncomputable def E89RS1 : RelationCertificate Table 3 ![![89, 0, 0], ![-11, 1, 0]]
  ![-2885, -119, 67] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![267, 0, 0], ![-33, 3, 0]]
    hsu := by decide
    w := ![![-8655, -357, 201], ![59394, 2571, -1404]]
    hw := by decide
    g := ![![![-461, -4661, -315], ![7637, 1600, 0]], ![![-455, -4963, -443], ![7738, 1600, 0]]]
    h := ![![![-94328, 8722, -37], ![-762937, 1120, 0]], ![![647348, -59837, 249], ![5235834, -7543, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {3} * I89N1 =  Ideal.span {B.equivFun.symm ![-2885, -119, 67]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E109RS1 : RelationCertificate Table 3 ![![109, 0, 0], ![-44, 1, 0]]
  ![31, 7, -2] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![327, 0, 0], ![-132, 3, 0]]
    hsu := by decide
    w := ![![93, 21, -6], ![384, 99, -27]]
    hw := by decide
    g := ![![![-5017, -54825, -4928], ![85337, 17640, 0]], ![![1416, 15231, 1368], ![-23701, -4900, 0]]]
    h := ![![![4655, -76, -2], ![11531, 72, 0]], ![![19144, -481, 3], ![47422, -112, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {3} * I109N1 =  Ideal.span {B.equivFun.symm ![31, 7, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 
