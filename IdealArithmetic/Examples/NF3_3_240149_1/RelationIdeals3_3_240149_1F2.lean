import IdealArithmetic.Examples.NF3_3_240149_1.PrimesBelow3_3_240149_1F2
import IdealArithmetic.Examples.NF3_3_240149_1.ClassGroupData3_3_240149_1

set_option linter.all false

noncomputable section


noncomputable def E89RS1 : RelationCertificate Table 2 ![![89, 0, 0], ![10, 1, 0]]
  ![-12, -1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![178, 0, 0], ![20, 2, 0]]
    hsu := by decide
    w := ![![-24, -2, 2], ![-50, 12, -4]]
    hw := by decide
    g := ![![![7814, -4, 39048], ![-1, -15620, 0]], ![![889, -1, 4437], ![0, -1775, 0]]]
    h := ![![![-11, -13, -6], ![86, 107, 0]], ![![-4, -26, -13], ![10, 231, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R89N1 : Ideal.span {2} * I89N1 =  Ideal.span {B.equivFun.symm ![-12, -1, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E89RS1 


noncomputable def E97RS1 : RelationCertificate Table 6 ![![97, 0, 0], ![-17, 1, 0]]
  ![-168, 1, 7] ![![6, 0, 0], ![0, 1, 0]] where
    su := ![![582, 0, 0], ![-102, 6, 0]]
    hsu := by decide
    w := ![![-1008, 6, 42], ![-342, 0, 12]]
    hw := by decide
    g := ![![![-2445220, -3, -12226118], ![5, 14671342, 0]], ![![427986, 0, 2139934], ![3, -2567921, 0]]]
    h := ![![![50510, -912885, 268551], ![-18250, -5209888, 0]], ![![17144, -309697, 91106], ![-6143, -1767456, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R97N1 : Ideal.span {6} * I97N1 =  Ideal.span {B.equivFun.symm ![-168, 1, 7]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E97RS1 


noncomputable def E101RS1 : RelationCertificate Table 3 ![![101, 0, 0], ![-25, 1, 0]]
  ![6, -2, 1] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![303, 0, 0], ![-75, 3, 0]]
    hsu := by decide
    w := ![![18, -6, 3], ![-51, 30, -9]]
    hw := by decide
    g := ![![![-42333, 0, -211868], ![1, 127120, 0]], ![![9676, 0, 48427], ![0, -29056, 0]]]
    h := ![![![-1, 45, -9], ![3, 182, 0]], ![![29, -136, 27], ![96, -546, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R101N1 : Ideal.span {3} * I101N1 =  Ideal.span {B.equivFun.symm ![6, -2, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E101RS1 
