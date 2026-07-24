import IdealArithmetic.Examples.NF3_1_138580_1.PrimesBelow3_1_138580_1F2
import IdealArithmetic.Examples.NF3_1_138580_1.ClassGroupData3_1_138580_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![-25, 1, 0]]
  ![254204, 178171, -134027] ![![2, 0, 0], ![3, 0, 1]] where
    su := ![![178, 0, 0], ![-50, 2, 0]]
    hsu := by decide
    w := ![![508408, 356342, -268054], ![9034006, -2456630, 566402]]
    hw := by decide
    g := ![![![197554864729, 57084561847, -81504237033], ![255580178583, -45440, 0]], ![![-42322893495, -12229420980, 17460952963], ![-54753863759, 12425, 0]]]
    h := ![![![28131763, -411263524, 63291761], ![-12523107, -1408275189, 0]], ![![515414498, -7535015970, 1159630901], ![-229442407, -25801716747, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![254204, 178171, -134027]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E89RS1 


noncomputable def E101RS1 : RelationCertificate Table 2 ![![101, 0, 0], ![-17, 1, 0]]
  ![8, 1, 1] ![![2, 0, 0], ![3, 0, 1]] where
    su := ![![202, 0, 0], ![-34, 2, 0]]
    hsu := by decide
    w := ![![16, 2, 2], ![130, 16, 8]]
    hw := by decide
    g := ![![![1017367, -39895, -578504], ![1236803, -79794, 0]], ![![-169562, 6649, 96417], ![-206133, 13299, 0]]]
    h := ![![![2671, -25018, 5561], ![-651, -140415, 0]], ![![21645, -203272, 45184], ![-5630, -1140895, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {2} * I101N1 =  Ideal.span {B.equivFun.symm ![8, 1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E101RS1 
