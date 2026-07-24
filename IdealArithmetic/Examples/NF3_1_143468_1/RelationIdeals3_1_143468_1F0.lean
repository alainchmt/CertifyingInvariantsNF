import IdealArithmetic.Examples.NF3_1_143468_1.PrimesBelow3_1_143468_1F0
import IdealArithmetic.Examples.NF3_1_143468_1.ClassGroupData3_1_143468_1

set_option linter.all false

noncomputable section


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![-23, 4, 1]]
  ![1, 0, 0] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![5, 0, 0], ![-23, 4, 1]]
    hsu := by decide
    w := ![![5, 0, 0], ![-23, 4, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![0, 1, 0]]
  ![-85, 7, 3] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![25, 0, 0], ![0, 5, 0]]
    hsu := by decide
    w := ![![-425, 35, 15], ![-575, -120, -5]]
    hw := by decide
    g := ![![![4, 25, -10], ![22, 0, 0]], ![![23, -38, 12], ![-23, 0, 0]]]
    h := ![![![-17, 1, 0], ![2, 3, 0]], ![![-23, -5, 0], ![1, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![-85, 7, 3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E13RS1 : RelationCertificate Table 5 ![![13, 0, 0], ![5, 1, 0]]
  ![-200, -17, 2] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![65, 0, 0], ![25, 5, 0]]
    hsu := by decide
    w := ![![-1000, -85, 10], ![5405, -870, -255]]
    hw := by decide
    g := ![![![15, -483, 183], ![-392, 0, 0]], ![![4, 59, -23], ![50, 0, 0]]]
    h := ![![![-2760, -671, -24], ![7136, 314, 0]], ![![14567, 3523, 124], ![-37658, -1663, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {5} * I13N1 =  Ideal.span {B.equivFun.symm ![-200, -17, 2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E23RS0 : RelationCertificate Table 5 ![![23, 0, 0], ![0, 1, 0]]
  ![0, 1, 0] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![115, 0, 0], ![0, 5, 0]]
    hsu := by decide
    w := ![![0, 5, 0], ![-115, 10, 5]]
    hw := by decide
    g := ![![![-44, -1, 0], ![14, 0, -1]], ![![1, 0, 0], ![0, 0, 0]]]
    h := ![![![0, 0, 0], ![1, 0, 0]], ![![-1, 0, 0], ![2, 1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {5} * I23N0 =  Ideal.span {B.equivFun.symm ![0, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS0 


noncomputable def E23RS2 : RelationCertificate Table 5 ![![23, 0, 0], ![-8, 1, 0]]
  ![15, -7, 1] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![115, 0, 0], ![-40, 5, 0]]
    hsu := by decide
    w := ![![75, -35, 5], ![-115, 40, -5]]
    hw := by decide
    g := ![![![23, -3, -1], ![-1, 0, 0]], ![![1, 0, 0], ![1, 0, 0]]]
    h := ![![![33, -4, 0], ![93, 1, 0]], ![![-25, 11, -1], ![-69, 22, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {5} * I23N2 =  Ideal.span {B.equivFun.symm ![15, -7, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS2 


noncomputable def E31RS0 : RelationCertificate Table 5 ![![31, 0, 0], ![-14, 1, 0]]
  ![20, 3, 0] ![![5, 0, 0], ![-23, 4, 1]] where
    su := ![![155, 0, 0], ![-70, 5, 0]]
    hsu := by decide
    w := ![![100, 15, 0], ![-805, 110, 35]]
    hw := by decide
    g := ![![![5, -9, 3], ![-6, 0, 0]], ![![20, 2, -3], ![9, 0, 0]]]
    h := ![![![1668, -133, 1], ![3692, -31, 0]], ![![-13279, 1078, -9], ![-29392, 286, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R31N0 : Ideal.span {5} * I31N0 =  Ideal.span {B.equivFun.symm ![20, 3, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E31RS0 
