import IdealArithmetic.MordellExamples.MordellExample142.NF2_2_568_1.PrimesBelow2_2_568_1F0
import IdealArithmetic.MordellExamples.MordellExample142.NF2_2_568_1.ClassGroupData2_2_568_1

namespace NF2_2_568_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0], ![0, 1]]
  ![12, 1] ![![1, 0]] where
    su := ![![2, 0], ![0, 1]]
    hsu := by decide
    w := ![![12, 1]]
    hw := by decide
    g := ![![![12, -1]], ![![-71, 6]]]
    h := ![![![6, 0], ![1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![12, 1]} * (J0 ^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0], ![1, 1]]
  ![-13, -1] ![![9, 0], ![5, 1]] where
    su := ![![27, 0], ![9, 9]]
    hsu := by decide
    w := ![![-117, -9], ![-207, -18]]
    hw := by decide
    g := ![![![-2, 0], ![1, 0]], ![![2, -1], ![5, 0]]]
    h := ![![![-4, 0], ![-1, 0]], ![![-7, 0], ![-2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![-13, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 1 ![![3, 0], ![2, 1]]
  ![1, 0] ![![3, 0], ![2, 1]] where
    su := ![![3, 0], ![2, 1]]
    hsu := by decide
    w := ![![3, 0], ![2, 1]]
    hw := by decide
    g := ![![![-1, -1], ![3, 0]], ![![0, 0], ![1, 0]]]
    h := ![![![-1, -1], ![3, 0]], ![![0, 0], ![1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {1} * I3N1 =  Ideal.span {B.equivFun.symm ![1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 3 ![![7, 0], ![3, 1]]
  ![-11, 1] ![![3, 0], ![2, 1]] where
    su := ![![21, 0], ![9, 3]]
    hsu := by decide
    w := ![![-33, 3], ![120, -9]]
    hw := by decide
    g := ![![![1, -1], ![4, 0]], ![![5, -1], ![5, 0]]]
    h := ![![![-2, 0], ![1, 0]], ![![4, -1], ![4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3} * I7N0 =  Ideal.span {B.equivFun.symm ![-11, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 9 ![![7, 0], ![4, 1]]
  ![47, -4] ![![9, 0], ![5, 1]] where
    su := ![![63, 0], ![36, 9]]
    hsu := by decide
    w := ![![423, -36], ![-333, 27]]
    hw := by decide
    g := ![![![-8, -1], ![5, 0]], ![![-12, -1], ![0, 0]]]
    h := ![![![5, -1], ![3, 0]], ![![-7, 0], ![3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {9} * I7N1 =  Ideal.span {B.equivFun.symm ![47, -4]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1

end

end NF2_2_568_1
