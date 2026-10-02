import IdealArithmetic.MordellExamples.MordellExample79.NF2_2_316_1.PrimesBelow2_2_316_1F0
import IdealArithmetic.MordellExamples.MordellExample79.NF2_2_316_1.ClassGroupData2_2_316_1

namespace NF2_2_316_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0], ![1, 1]]
  ![9, 1] ![![1, 0]] where
    su := ![![2, 0], ![1, 1]]
    hsu := by decide
    w := ![![9, 1]]
    hw := by decide
    g := ![![![9, -1]], ![![-35, 4]]]
    h := ![![![3, -1], ![3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![9, 1]} * (J0 ^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0 E2RS0 


noncomputable def E3RS0 : RelationCertificate Table 9 ![![3, 0], ![1, 1]]
  ![17, 2] ![![9, 0], ![5, 1]] where
    su := ![![27, 0], ![9, 9]]
    hsu := by decide
    w := ![![153, 18], ![243, 27]]
    hw := by decide
    g := ![![![-3, 0], ![2, 0]], ![![3, -1], ![4, 0]]]
    h := ![![![5, 0], ![2, 0]], ![![8, 0], ![3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {9} * I3N0 =  Ideal.span {B.equivFun.symm ![17, 2]} * (J0 ^ 2) := by
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


noncomputable def E5RS0 : RelationCertificate Table 3 ![![5, 0], ![2, 1]]
  ![8, -1] ![![3, 0], ![2, 1]] where
    su := ![![15, 0], ![6, 3]]
    hsu := by decide
    w := ![![24, -3], ![-63, 6]]
    hw := by decide
    g := ![![![-2, 0], ![-1, 0]], ![![-5, 0], ![-2, 0]]]
    h := ![![![0, -1], ![4, 0]], ![![-5, 0], ![2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {3} * I5N0 =  Ideal.span {B.equivFun.symm ![8, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 9 ![![5, 0], ![3, 1]]
  ![-19, 2] ![![9, 0], ![5, 1]] where
    su := ![![45, 0], ![27, 9]]
    hsu := by decide
    w := ![![-171, 18], ![63, -9]]
    hw := by decide
    g := ![![![-6, -1], ![7, 0]], ![![-7, -1], ![4, 0]]]
    h := ![![![-5, 0], ![2, 0]], ![![-1, -1], ![4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {9} * I5N1 =  Ideal.span {B.equivFun.symm ![-19, 2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 3 ![![7, 0], ![3, 1]]
  ![-10, -1] ![![3, 0], ![2, 1]] where
    su := ![![21, 0], ![9, 3]]
    hsu := by decide
    w := ![![-30, -3], ![-99, -12]]
    hw := by decide
    g := ![![![-4, 0], ![1, 0]], ![![1, -1], ![2, 0]]]
    h := ![![![-4, -1], ![6, 0]], ![![-6, -1], ![3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {3} * I7N0 =  Ideal.span {B.equivFun.symm ![-10, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 9 ![![7, 0], ![4, 1]]
  ![-4, -1] ![![9, 0], ![5, 1]] where
    su := ![![63, 0], ![36, 9]]
    hsu := by decide
    w := ![![-36, -9], ![-99, -9]]
    hw := by decide
    g := ![![![-4, -1], ![8, 0]], ![![-1, 0], ![0, 0]]]
    h := ![![![-4, -1], ![6, 0]], ![![-5, -1], ![6, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {9} * I7N1 =  Ideal.span {B.equivFun.symm ![-4, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1

end

end NF2_2_316_1
