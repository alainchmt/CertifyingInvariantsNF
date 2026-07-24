import IdealArithmetic.Examples.NF3_3_600925_1.PrimesBelow3_3_600925_1F3
import IdealArithmetic.Examples.NF3_3_600925_1.ClassGroupData3_3_600925_1

set_option linter.all false

noncomputable section


noncomputable def E139RS0 : RelationCertificate Table 3 ![![139, 0, 0], ![16, 1, 0]]
  ![85, 4, -2] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![417, 0, 0], ![48, 3, 0]]
    hsu := by decide
    w := ![![255, 12, -6], ![-1674, -66, 39]]
    hw := by decide
    g := ![![![113, 971, 86], ![-1504, -311, 0]], ![![22, 116, 10], ![-178, -37, 0]]]
    h := ![![![3151, 187, -2], ![-27369, 92, 0]], ![![-20906, -1332, -5], ![181586, 236, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N0 : Ideal.span {3} * I139N0 =  Ideal.span {B.equivFun.symm ![85, 4, -2]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS0 


noncomputable def E139RS1 : RelationCertificate Table 3 ![![139, 0, 0], ![45, 1, 0]]
  ![5965, 1432, -380] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![417, 0, 0], ![135, 3, 0]]
    hsu := by decide
    w := ![![17895, 4296, -1140], ![85602, 20598, -5463]]
    hw := by decide
    g := ![![![-43, -191, 68], ![604, 143, 0]], ![![-1, -38, 32], ![192, 47, 0]]]
    h := ![![![-30335, -566, 4], ![93834, -312, 0]], ![![-144764, -2584, 27], ![447794, -1858, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N1 : Ideal.span {3} * I139N1 =  Ideal.span {B.equivFun.symm ![5965, 1432, -380]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS1 


noncomputable def E139RS2 : RelationCertificate Table 3 ![![139, 0, 0], ![-62, 1, 0]]
  ![-120539, -44351, -11339] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![417, 0, 0], ![-186, 3, 0]]
    hsu := by decide
    w := ![![-361617, -133053, -34017], ![-1203582, -442845, -113220]]
    hw := by decide
    g := ![![![-138415, -1503451, -135192], ![2341430, 483750, 0]], ![![60832, 660440, 59386], ![-1028569, -212500, 0]]]
    h := ![![![-20135625, 376503, -2561], ![-45140828, 114880, 0]], ![![-67018234, 1253112, -8523], ![-150244086, 382319, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R139N2 : Ideal.span {3} * I139N2 =  Ideal.span {B.equivFun.symm ![-120539, -44351, -11339]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E139RS2 


noncomputable def E149RS1 : RelationCertificate Table 3 ![![149, 0, 0], ![-35, 1, 0]]
  ![53, -22, -10] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![447, 0, 0], ![-105, 3, 0]]
    hsu := by decide
    w := ![![159, -66, -30], ![-3342, -384, -9]]
    hw := by decide
    g := ![![![-53, -1513, 28], ![1750, 287, 0]], ![![27, 394, -14], ![-430, -67, 0]]]
    h := ![![![5427, -132, -2], ![23102, 96, 0]], ![![-112886, 3404, -15], ![-480540, 744, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R149N1 : Ideal.span {3} * I149N1 =  Ideal.span {B.equivFun.symm ![53, -22, -10]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E149RS1 


noncomputable def E163RS1 : RelationCertificate Table 9 ![![163, 0, 0], ![-21, 1, 0]]
  ![-1124417, -413717, -105773] ![![9, 0, 0], ![-27, -2, 1]] where
    su := ![![1467, 0, 0], ![-189, 9, 0]]
    hsu := by decide
    w := ![![-10119753, -3723453, -951957], ![-14600565, -5372118, -1373463]]
    hw := by decide
    g := ![![![-2133, -2643, 42], ![7012, 1286, 0]], ![![303, 387, -15], ![-954, -163, 0]]]
    h := ![![![-218367443, 10572801, -24815], ![-1694893752, 1313024, 0]], ![![-315055895, 15254208, -35802], ![-2445356600, 1894373, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R163N1 : Ideal.span {9} * I163N1 =  Ideal.span {B.equivFun.symm ![-1124417, -413717, -105773]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E163RS1 


noncomputable def E167RS1 : RelationCertificate Table 3 ![![167, 0, 0], ![30, 1, 0]]
  ![-77, -14, 4] ![![3, 0, 0], ![-30, -2, 1]] where
    su := ![![501, 0, 0], ![90, 3, 0]]
    hsu := by decide
    w := ![![-231, -42, 12], ![-318, -168, 39]]
    hw := by decide
    g := ![![![55, 586, 55], ![-901, -186, 0]], ![![28, 112, 10], ![-168, -35, 0]]]
    h := ![![![-61, -12, -1], ![337, 57, 0]], ![![-38, -12, -1], ![208, 60, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R167N1 : Ideal.span {3} * I167N1 =  Ideal.span {B.equivFun.symm ![-77, -14, 4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E167RS1 
