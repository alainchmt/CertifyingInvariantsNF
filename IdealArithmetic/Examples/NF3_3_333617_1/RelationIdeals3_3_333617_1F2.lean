import IdealArithmetic.Examples.NF3_3_333617_1.PrimesBelow3_3_333617_1F2
import IdealArithmetic.Examples.NF3_3_333617_1.ClassGroupData3_3_333617_1

set_option linter.all false

noncomputable section


noncomputable def E101RS0 : RelationCertificate Table 3 ![![101, 0, 0], ![33, 1, 0]]
  ![-37, 5, 0] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![303, 0, 0], ![99, 3, 0]]
    hsu := by decide
    w := ![![-111, 15, 0], ![1422, 117, -42]]
    hw := by decide
    g := ![![![18, -59, -11], ![8, 0, 0]], ![![26, -23, -5], ![5, 0, 0]]]
    h := ![![![-464, -47, -1], ![1419, 101, 0]], ![![5418, 169, 0], ![-16568, -14, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N0 : Ideal.span {3} * I101N0 =  Ideal.span {B.equivFun.symm ![-37, 5, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS0 


noncomputable def E101RS1 : RelationCertificate Table 3 ![![101, 0, 0], ![-32, 1, 0]]
  ![-51, -2, 1] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![303, 0, 0], ![-96, 3, 0]]
    hsu := by decide
    w := ![![-153, -6, 3], ![1416, 27, -33]]
    hw := by decide
    g := ![![![0, 15, -2], ![-2, 0, 0]], ![![23, -5, 0], ![3, 0, 0]]]
    h := ![![![-5175, 194, -1], ![-16332, 102, 0]], ![![48376, -1611, 3], ![152672, -314, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {3} * I101N1 =  Ideal.span {B.equivFun.symm ![-51, -2, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 


noncomputable def E107RS1 : RelationCertificate Table 3 ![![107, 0, 0], ![48, 1, 0]]
  ![-48, -23, 4] ![![3, 0, 0], ![-31, -1, 1]] where
    su := ![![321, 0, 0], ![144, 3, 0]]
    hsu := by decide
    w := ![![-144, -69, 12], ![3, -288, 39]]
    hw := by decide
    g := ![![![16, 73, 12], ![-5, 0, 0]], ![![15, 38, 6], ![-2, 0, 0]]]
    h := ![![![-528, -61, -1], ![1176, 111, 0]], ![![-13, -7, 0], ![29, 13, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R107N1 : Ideal.span {3} * I107N1 =  Ideal.span {B.equivFun.symm ![-48, -23, 4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E107RS1 
