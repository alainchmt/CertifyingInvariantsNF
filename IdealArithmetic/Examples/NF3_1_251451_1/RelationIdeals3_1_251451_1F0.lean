import IdealArithmetic.Examples.NF3_1_251451_1.PrimesBelow3_1_251451_1F0
import IdealArithmetic.Examples.NF3_1_251451_1.ClassGroupData3_1_251451_1

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

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![1, 1, 0]]
  ![-377, -13, -10] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![4, 0, 0], ![2, 2, 0]]
    hsu := by decide
    w := ![![-754, -26, -20], ![-10552, -364, -280]]
    hw := by decide
    g := ![![![-14, 0, 0], ![1, 0, 0]], ![![-1, -10, 0], ![1, 0, 0]]]
    h := ![![![-252, -100, -35], ![127, 60, 0]], ![![-3518, -1384, -483], ![1760, 826, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![-377, -13, -10]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E2RS1 


noncomputable def E7RS0 : RelationCertificate Table 1 ![![7, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![7, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![7, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {1} * I7N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 7 ![![7, 0, 0], ![22, 0, 1]]
  ![36, 0, 1] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![49, 0, 0], ![154, 0, 7]]
    hsu := by decide
    w := ![![252, 0, 7], ![49, 0, 0]]
    hw := by decide
    g := ![![![0, 0, 0], ![1, 0, 0]], ![![1, -1, 0], ![5, 0, 0]]]
    h := ![![![-20, 0, -1], ![8, 0, 0]], ![![-21, 0, -1], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {7} * I7N1 =  Ideal.span {B.equivFun.symm ![36, 0, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E7RS1 


noncomputable def E13RS1 : RelationCertificate Table 14 ![![13, 0, 0], ![6, 1, 0]]
  ![-38557, -1330, -1023] ![![14, 0, 0], ![21, 1, 1]] where
    su := ![![182, 0, 0], ![84, 14, 0]]
    hsu := by decide
    w := ![![-539798, -18620, -14322], ![-924994, -31906, -24542]]
    hw := by decide
    g := ![![![-31251, 33141, 1174], ![-44417, 27962, 0]], ![![-17054, 18079, 641], ![-24225, 15252, 0]]]
    h := ![![![-1159033, -286058, -15625], ![2504812, 202102, 0]], ![![-1986095, -490185, -26775], ![4292194, 346322, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {14} * I13N1 =  Ideal.span {B.equivFun.symm ![-38557, -1330, -1023]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E13RS1 


noncomputable def E19RS1 : RelationCertificate Table 14 ![![19, 0, 0], ![9, 1, 0]]
  ![8, -7, 1] ![![14, 0, 0], ![21, 1, 1]] where
    su := ![![266, 0, 0], ![126, 14, 0]]
    hsu := by decide
    w := ![![112, -98, 14], ![-126, 126, -14]]
    hw := by decide
    g := ![![![31, -36, -2], ![69, -30, 0]], ![![9, -27, -2], ![56, -22, 0]]]
    h := ![![![260, 46, 2], ![-548, -37, 0]], ![![-315, -61, -3], ![664, 56, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {14} * I19N1 =  Ideal.span {B.equivFun.symm ![8, -7, 1]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E19RS1 


noncomputable def E23RS0 : RelationCertificate Table 2 ![![23, 0, 0], ![3, 1, 0]]
  ![10, -9, 1] ![![2, 0, 0], ![25, 1, 1]] where
    su := ![![46, 0, 0], ![6, 2, 0]]
    hsu := by decide
    w := ![![20, -18, 2], ![-142, 122, -10]]
    hw := by decide
    g := ![![![-29, 10, 26], ![-159, 0, 0]], ![![-27, 1, 4], ![-28, 0, 0]]]
    h := ![![![8, 2, 0], ![-58, 1, 0]], ![![-73, -23, -1], ![536, 18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {2} * I23N0 =  Ideal.span {B.equivFun.symm ![10, -9, 1]} * (J0 ^ 1*J1^ 0) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_0 E23RS0 


noncomputable def E23RS1 : RelationCertificate Table 7 ![![23, 0, 0], ![7, 1, 0]]
  ![-20, 14, 1] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![161, 0, 0], ![49, 7, 0]]
    hsu := by decide
    w := ![![-140, 98, 7], ![49, -56, 14]]
    hw := by decide
    g := ![![![-194, -7, -2418], ![2, 16890, 0]], ![![-70, -3, -967], ![4, 6756, 0]]]
    h := ![![![-52, -14, -1], ![168, 24, 0]], ![![7, 0, 0], ![-22, 2, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {7} * I23N1 =  Ideal.span {B.equivFun.symm ![-20, 14, 1]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E23RS1 


noncomputable def E23RS2 : RelationCertificate Table 14 ![![23, 0, 0], ![-10, 1, 0]]
  ![1, 7, -6] ![![14, 0, 0], ![21, 1, 1]] where
    su := ![![322, 0, 0], ![-140, 14, 0]]
    hsu := by decide
    w := ![![14, 98, -84], ![70, -182, 98]]
    hw := by decide
    g := ![![![108079, -114792, -4069], ![153652, -96879, 0]], ![![-45258, 48052, 1703], ![-64323, 40554, 0]]]
    h := ![![![17, 6, -1], ![39, 17, 0]], ![![25, 0, 0], ![57, 7, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N2 : Ideal.span {14} * I23N2 =  Ideal.span {B.equivFun.symm ![1, 7, -6]} * (J0 ^ 1*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1J1_1 E23RS2 


noncomputable def E29RS1 : RelationCertificate Table 7 ![![29, 0, 0], ![9, 1, 0]]
  ![-604, -21, -16] ![![7, 0, 0], ![0, 1, 0]] where
    su := ![![203, 0, 0], ![63, 7, 0]]
    hsu := by decide
    w := ![![-4228, -147, -112], ![-784, -28, -21]]
    hw := by decide
    g := ![![![-4, 2, -13], ![6, 92, 0]], ![![-1, 0, -4], ![4, 29, 0]]]
    h := ![![![-1850, -235, -4], ![5894, 100, 0]], ![![-344, -46, -1], ![1096, 26, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {7} * I29N1 =  Ideal.span {B.equivFun.symm ![-604, -21, -16]} * (J0 ^ 0*J1^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_0J1_1 E29RS1 
