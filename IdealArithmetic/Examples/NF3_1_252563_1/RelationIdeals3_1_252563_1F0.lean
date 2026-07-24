import IdealArithmetic.Examples.NF3_1_252563_1.PrimesBelow3_1_252563_1F0
import IdealArithmetic.Examples.NF3_1_252563_1.ClassGroupData3_1_252563_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![25, 1, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![2, 0, 0], ![25, 1, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![25, 1, 1]]
    hw := by decide
    g := ![![![-24, -1, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![-24, -1, -1], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![1, -1, 0] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![2, -2, 0], ![-10, 14, 0]]
    hw := by decide
    g := ![![![-18, -1, -1], ![3, 0, 0]], ![![-19, -1, -1], ![3, 0, 0]]]
    h := ![![![0, -1, 0], ![1, 0, 0]], ![![-4, 1, -1], ![3, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![1, -1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![2, 1, 0]]
  ![2046851, 47555, 52736] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![14, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![4093702, 95110, 105472], ![54681460, 1270428, 1408838]]
    hw := by decide
    g := ![![![-18, 30, 71], ![-5, 0, 0]], ![![7, -388, 11], ![25, 0, 0]]]
    h := ![![![4786551, 2491340, 126271], ![-15729503, -831161, 0]], ![![63936194, 33278002, 1686666], ![-210106314, -11102243, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![2046851, 47555, 52736]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E7RS2 : RelationCertificate Table 2 ![![7, 0, 0], ![-2, 1, 0]]
  ![-14804628662, -343959631, -381433185] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![14, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![-29609257324, -687919262, -762866370], ![-395504465110, -9188853904, -10189956888]]
    hw := by decide
    g := ![![![-196, -1968, 5988], ![-217, 0, 0]], ![![1616, -32884, -3121], ![2289, 0, 0]]]
    h := ![![![-58593759594, 29915180961, -916946320], ![-197675844248, 6037191055, 0]], ![![-782663789691, 399590827781, -12248073619], ![-2640447147641, 80641536889, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N2 : Ideal.span {2} * I7N2 =  Ideal.span {B.equivFun.symm ![-14804628662, -343959631, -381433185]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS2 


noncomputable def E17RS1 : RelationCertificate Table 2 ![![17, 0, 0], ![2, 1, 0]]
  ![503, -198, -399] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![34, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![1006, -396, -798], ![-8320, 4274, 5492]]
    hw := by decide
    g := ![![![-923691, 2009576, 1700621], ![-9690781, 0, 0]], ![![-157681, 343017, 290281], ![-1654133, 0, 0]]]
    h := ![![![1367, 666, -19], ![-11368, -76, 0]], ![![-11320, -5503, 116], ![94140, 774, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![503, -198, -399]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E29RS1 : RelationCertificate Table 2 ![![29, 0, 0], ![13, 1, 0]]
  ![-1472, 2315, -757] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![58, 0, 0], ![26, 2, 0]]
    hsu := by decide
    w := ![![-2944, 4630, -1514], ![17730, -29296, 10684]]
    hw := by decide
    g := ![![![3821343, -8313927, -7035733], ![40092249, 0, 0]], ![![1831831, -3985455, -3372726], ![19219058, 0, 0]]]
    h := ![![![-4382, -343, -33], ![9662, 200, 0]], ![![26160, 2014, 225], ![-57675, -1183, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2} * I29N1 =  Ideal.span {B.equivFun.symm ![-1472, 2315, -757]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 
