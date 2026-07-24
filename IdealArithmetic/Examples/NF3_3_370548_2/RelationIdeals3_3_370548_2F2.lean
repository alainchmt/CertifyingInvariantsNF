import IdealArithmetic.Examples.NF3_3_370548_2.PrimesBelow3_3_370548_2F2
import IdealArithmetic.Examples.NF3_3_370548_2.ClassGroupData3_3_370548_2

set_option linter.all false

noncomputable section


noncomputable def E103RS1 : RelationCertificate Table 5 ![![103, 0, 0], ![38, 1, 0]]
  ![901, 34, -21] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![515, 0, 0], ![190, 5, 0]]
    hsu := by decide
    w := ![![4505, 170, -105], ![-4700, -175, 110]]
    hw := by decide
    g := ![![![-287, -3675, 3793], ![-618, -9476, 0]], ![![-102, -1346, 1390], ![-227, -3473, 0]]]
    h := ![![![5549, 131, -1], ![-15017, 41, 0]], ![![-5884, -197, -2], ![15924, 114, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R103N1 : Ideal.span {5} * I103N1 =  Ideal.span {B.equivFun.symm ![901, 34, -21]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E103RS1 


noncomputable def E109RS1 : RelationCertificate Table 5 ![![109, 0, 0], ![21, 1, 0]]
  ![481, 19, -11] ![![5, 0, 0], ![-2, 1, 0]] where
    su := ![![545, 0, 0], ![105, 5, 0]]
    hsu := by decide
    w := ![![2405, 95, -55], ![-2480, -85, 60]]
    hw := by decide
    g := ![![![-137, -192, 165], ![18, -392, 0]], ![![-17, -36, 33], ![1, -80, 0]]]
    h := ![![![2173, 94, -1], ![-11256, 49, 0]], ![![-2308, -132, -2], ![11956, 115, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R109N1 : Ideal.span {5} * I109N1 =  Ideal.span {B.equivFun.symm ![481, 19, -11]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E109RS1 


noncomputable def E113RS1 : RelationCertificate Table 25 ![![113, 0, 0], ![19, 1, 0]]
  ![-53, -7, 3] ![![25, 0, 0], ![-12, 1, 0]] where
    su := ![![2825, 0, 0], ![475, 25, 0]]
    hsu := by decide
    w := ![![-1325, -175, 75], ![1050, 175, -50]]
    hw := by decide
    g := ![![![678341, 43470454, -7254497], ![1413232, 90681216, 0]], ![![125209, 8023752, -1339031], ![260855, 16737888, 0]]]
    h := ![![![-61, -13, -1], ![360, 58, 0]], ![![34, -17, -2], ![-200, 112, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R113N1 : Ideal.span {25} * I113N1 =  Ideal.span {B.equivFun.symm ![-53, -7, 3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E113RS1 
