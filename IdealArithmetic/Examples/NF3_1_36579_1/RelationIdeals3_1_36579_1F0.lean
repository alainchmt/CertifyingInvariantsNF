import IdealArithmetic.Examples.NF3_1_36579_1.PrimesBelow3_1_36579_1F0
import IdealArithmetic.Examples.NF3_1_36579_1.ClassGroupData3_1_36579_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 1 ![![2, 0, 0], ![-5, 1, 1]]
  ![1, 0, 0] ![![2, 0, 0], ![-5, 1, 1]] where
    su := ![![2, 0, 0], ![-5, 1, 1]]
    hsu := by decide
    w := ![![2, 0, 0], ![-5, 1, 1]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {1} * I2N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 2 ![![2, 0, 0], ![0, 1, 0]]
  ![12, -8, -3] ![![2, 0, 0], ![-5, 1, 1]] where
    su := ![![4, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![24, -16, -6], ![500, 74, -16]]
    hw := by decide
    g := ![![![-44, 88, -87], ![113, 0, 0]], ![![85, -165, 162], ![-210, 0, 0]]]
    h := ![![![6, -4, 0], ![0, -3, 0]], ![![125, 14, 0], ![9, -8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {2} * I2N1 =  Ideal.span {B.equivFun.symm ![12, -8, -3]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 2 ![![5, 0, 0], ![0, 1, 0]]
  ![610, -270, 57] ![![2, 0, 0], ![-5, 1, 1]] where
    su := ![![10, 0, 0], ![0, 2, 0]]
    hsu := by decide
    w := ![![1220, -540, 114], ![3190, -1412, 298]]
    hw := by decide
    g := ![![![-7, -18, -6], ![9, 0, 0]], ![![2, -6, -1], ![-4, 0, 0]]]
    h := ![![![122, -52, 0], ![-10, 57, 0]], ![![319, -136, 0], ![-26, 149, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2} * I5N0 =  Ideal.span {B.equivFun.symm ![610, -270, 57]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS2 : RelationCertificate Table 2 ![![5, 0, 0], ![-2, 1, 0]]
  ![14, 0, -1] ![![2, 0, 0], ![-5, 1, 1]] where
    su := ![![10, 0, 0], ![-4, 2, 0]]
    hsu := by decide
    w := ![![28, 0, -2], ![10, 40, 10]]
    hw := by decide
    g := ![![![10, -11, 9], ![-11, 0, 0]], ![![-3, 11, -12], ![16, 0, 0]]]
    h := ![![![62, -32, 1], ![148, -6, 0]], ![![13, -2, 1], ![30, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N2 : Ideal.span {2} * I5N2 =  Ideal.span {B.equivFun.symm ![14, 0, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS2 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![-8, -3, 1]]
  ![-83026, 36746, -7757] ![![2, 0, 0], ![-5, 1, 1]] where
    su := ![![14, 0, 0], ![-16, -6, 2]]
    hsu := by decide
    w := ![![-166052, 73492, -15514], ![-434150, 192148, -40562]]
    hw := by decide
    g := ![![![23, 76, 20], ![-7, 0, 0]], ![![-77, -194, -61], ![78, 0, 0]]]
    h := ![![![-6782, 7154, -1743], ![4444, 0, 0]], ![![-17741, 18701, -4556], ![11611, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![-83026, 36746, -7757]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![2, 1, 0]]
  ![-16446, 267, 1249] ![![2, 0, 0], ![-5, 1, 1]] where
    su := ![![14, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![-32892, 534, 2498], ![-28370, -48386, -10916]]
    hw := by decide
    g := ![![![-7363232, 14488505, -14271266], ![18516713, 0, 0]], ![![1827288, -3595513, 3541600], ![-4595162, 0, 0]]]
    h := ![![![-38318, -19871, -784], ![125890, 6737, 0]], ![![-38477, -23048, -1463], ![127577, 4783, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![-16446, 267, 1249]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E17RS1 : RelationCertificate Table 2 ![![17, 0, 0], ![6, 1, 0]]
  ![-6026, 2667, -563] ![![2, 0, 0], ![-5, 1, 1]] where
    su := ![![34, 0, 0], ![12, 2, 0]]
    hsu := by decide
    w := ![![-12052, 5334, -1126], ![-31510, 13946, -2944]]
    hw := by decide
    g := ![![![-62, -59, -34], ![121, 0, 0]], ![![-36, -41, -20], ![62, 0, 0]]]
    h := ![![![-5854, -897, -56], ![15582, 389, 0]], ![![-15313, -2344, -146], ![40761, 1010, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {2} * I17N1 =  Ideal.span {B.equivFun.symm ![-6026, 2667, -563]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E19RS1 : RelationCertificate Table 2 ![![19, 0, 0], ![-7, 1, 0]]
  ![-34862, -10061, -196] ![![2, 0, 0], ![-5, 1, 1]] where
    su := ![![38, 0, 0], ![-14, 2, 0]]
    hsu := by decide
    w := ![![-69724, -20122, -392], ![592430, -49888, -55768]]
    hw := by decide
    g := ![![![70573933, -138867037, 136784863], ![-177475913, 0, 0]], ![![-39882224, 78475527, -77298865], ![100293895, 0, 0]]]
    h := ![![![-487934, 75540, -957], ![-1319412, 17987, 0]], ![![4187353, -652905, 6479], ![11323356, -150985, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R19N1 : Ideal.span {2} * I19N1 =  Ideal.span {B.equivFun.symm ![-34862, -10061, -196]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E19RS1 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![-11, 1, 0]]
  ![223646754, -98982519, 20894989] ![![2, 0, 0], ![-5, 1, 1]] where
    su := ![![46, 0, 0], ![-22, 2, 0]]
    hsu := by decide
    w := ![![447293508, -197965038, 41789978], ![1169467870, -517587998, 109261672]]
    hw := by decide
    g := ![![![-14638, -24299, -9172], ![19861, 0, 0]], ![![6241, 8945, 3683], ![-9275, 0, 0]]]
    h := ![![![5100751690, -545831884, 8063712], ![10644876556, -164570387, 0]], ![![13336131869, -1427100643, 21082918], ![27831481732, -430276278, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![223646754, -98982519, 20894989]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 
