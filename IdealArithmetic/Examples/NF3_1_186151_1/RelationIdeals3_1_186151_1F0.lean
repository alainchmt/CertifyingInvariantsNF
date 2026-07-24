import IdealArithmetic.Examples.NF3_1_186151_1.PrimesBelow3_1_186151_1F0
import IdealArithmetic.Examples.NF3_1_186151_1.ClassGroupData3_1_186151_1

set_option linter.all false

noncomputable section


noncomputable def E3RS0 : RelationCertificate Table 1 ![![3, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![3, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![3, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N0 : Ideal.span {1} * I3N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E3RS0 


noncomputable def E3RS1 : RelationCertificate Table 9 ![![3, 0, 0], ![-50, -6, 1]]
  ![-41, -6, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![27, 0, 0], ![-450, -54, 9]]
    hsu := by decide
    w := ![![-369, -54, 9], ![396, 54, -9]]
    hw := by decide
    g := ![![![2209, 66227, -22321], ![6625, 200889, 0]], ![![-35321, -1059638, 357137], ![-105960, -3214233, 0]]]
    h := ![![![3, 0, 0], ![1, 0, 0]], ![![48, 6, -1], ![2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R3N1 : Ideal.span {9} * I3N1 =  Ideal.span {B.equivFun.symm ![-41, -6, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E3RS1 


noncomputable def E7RS0 : RelationCertificate Table 9 ![![7, 0, 0], ![0, 1, 0]]
  ![49, -15, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![63, 0, 0], ![0, 9, 0]]
    hsu := by decide
    w := ![![441, -135, 9], ![126, 171, -18]]
    hw := by decide
    g := ![![![-27, -12, -2], ![17, 7, 0]], ![![-43, -19, -2], ![14, 2, 0]]]
    h := ![![![7, -3, 0], ![6, 1, 0]], ![![2, 2, 0], ![5, -2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {9} * I7N0 =  Ideal.span {B.equivFun.symm ![49, -15, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS0 


noncomputable def E11RS0 : RelationCertificate Table 9 ![![11, 0, 0], ![-50, -7, 1]]
  ![2381, 906, 89] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![99, 0, 0], ![-450, -63, 9]]
    hsu := by decide
    w := ![![21429, 8154, 801], ![17154, 6516, 639]]
    hw := by decide
    g := ![![![-780, -24904, 8395], ![-2506, -75565, 0]], ![![3882, 114015, -38426], ![11383, 345821, 0]]]
    h := ![![![21, 55, 12], ![-43, 0, 0]], ![![46, 48, 9], ![-28, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {9} * I11N0 =  Ideal.span {B.equivFun.symm ![2381, 906, 89]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 3 ![![11, 0, 0], ![-4, 1, 0]]
  ![-134, -51, -5] ![![3, 0, 0], ![0, 1, 0]] where
    su := ![![33, 0, 0], ![-12, 3, 0]]
    hsu := by decide
    w := ![![-402, -153, -15], ![-1365, -519, -51]]
    hw := by decide
    g := ![![![59, 0, -5], ![3, 13, 0]], ![![-38, 0, 1], ![1, -2, 0]]]
    h := ![![![-218, 53, -2], ![-566, 17, 0]], ![![-745, 178, -6], ![-1935, 49, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {3} * I11N1 =  Ideal.span {B.equivFun.symm ![-134, -51, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E23RS1 : RelationCertificate Table 9 ![![23, 0, 0], ![3, 1, 0]]
  ![-50, -6, 1] ![![9, 0, 0], ![-3, 1, 0]] where
    su := ![![207, 0, 0], ![27, 9, 0]]
    hsu := by decide
    w := ![![-450, -54, 9], ![423, 45, -9]]
    hw := by decide
    g := ![![![1988, 59447, -20036], ![5949, 180323, 0]], ![![368, 11031, -3718], ![1106, 33462, 0]]]
    h := ![![![-52, -20, -1], ![382, 24, 0]], ![![43, 14, 0], ![-314, -1, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {9} * I23N1 =  Ideal.span {B.equivFun.symm ![-50, -6, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS1 
