import IdealArithmetic.Examples.NF3_1_532652_1.PrimesBelow3_1_532652_1F4
import IdealArithmetic.Examples.NF3_1_532652_1.ClassGroupData3_1_532652_1

set_option linter.all false

noncomputable section


noncomputable def E197RS0 : RelationCertificate Table 35 ![![197, 0, 0], ![26, 1, 0]]
  ![-7685, -901, 181] ![![35, 0, 0], ![-48, 11, 1]] where
    su := ![![6895, 0, 0], ![910, 35, 0]]
    hsu := by decide
    w := ![![-268975, -31535, 6335], ![632660, 72275, -14700]]
    hw := by decide
    g := ![![![32809, 38927, 3962], ![-32588, 0, 0]], ![![5918, 7005, 713], ![-5858, 0, 0]]]
    h := ![![![-5624737, -220913, -175], ![42617904, 34656, 0]], ![![13229856, 519589, 411], ![-100240906, -81387, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N0 : Ideal.span {35} * I197N0 =  Ideal.span {B.equivFun.symm ![-7685, -901, 181]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E197RS0 


noncomputable def E197RS1 : RelationCertificate Table 35 ![![197, 0, 0], ![85, 1, 0]]
  ![49197, 18209, 1924] ![![35, 0, 0], ![-48, 11, 1]] where
    su := ![![6895, 0, 0], ![2975, 35, 0]]
    hsu := by decide
    w := ![![1721895, 637315, 67340], ![7166810, 2652615, 280280]]
    hw := by decide
    g := ![![![811, 353, -1], ![-976, 0, 0]], ![![353, 145, -1], ![-393, 0, 0]]]
    h := ![![![880316, 12421, 33], ![-2039683, -4577, 0]], ![![3663988, 51668, 137], ![-8489422, -18981, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R197N1 : Ideal.span {35} * I197N1 =  Ideal.span {B.equivFun.symm ![49197, 18209, 1924]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E197RS1 


noncomputable def E199RS1 : RelationCertificate Table 7 ![![199, 0, 0], ![21, 1, 0]]
  ![665, 246, 26] ![![7, 0, 0], ![-41, -3, 1]] where
    su := ![![1393, 0, 0], ![147, 7, 0]]
    hsu := by decide
    w := ![![4655, 1722, 182], ![13391, 4963, 525]]
    hw := by decide
    g := ![![![56, -31, 5], ![-73, 0, 0]], ![![21, -1, 0], ![-4, 0, 0]]]
    h := ![![![1274, 59, 0], ![-12041, 26, 0]], ![![3734, 173, 0], ![-35293, 75, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R199N1 : Ideal.span {7} * I199N1 =  Ideal.span {B.equivFun.symm ![665, 246, 26]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E199RS1 
