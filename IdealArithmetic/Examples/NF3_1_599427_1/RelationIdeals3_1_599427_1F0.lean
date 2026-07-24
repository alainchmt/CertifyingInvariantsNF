import IdealArithmetic.Examples.NF3_1_599427_1.PrimesBelow3_1_599427_1F0
import IdealArithmetic.Examples.NF3_1_599427_1.ClassGroupData3_1_599427_1

set_option linter.all false

noncomputable section


noncomputable def E5RS0 : RelationCertificate Table 1 ![![5, 0, 0], ![1, -1, 1]]
  ![1, 0, 0] ![![5, 0, 0], ![1, -1, 1]] where
    su := ![![5, 0, 0], ![1, -1, 1]]
    hsu := by decide
    w := ![![5, 0, 0], ![1, -1, 1]]
    hw := by decide
    g := ![![![0, 1, -1], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, 1, -1], ![5, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {1} * I5N0 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 5 ![![5, 0, 0], ![1, 1, 0]]
  ![-5874, -1108, -209] ![![5, 0, 0], ![1, -1, 1]] where
    su := ![![25, 0, 0], ![5, 5, 0]]
    hsu := by decide
    w := ![![-29370, -5540, -1045], ![-139825, -26375, -4975]]
    hw := by decide
    g := ![![![67, -12, -3], ![17, 0, 0]], ![![25, 12, -4], ![5, 0, 0]]]
    h := ![![![-1088, -1088, -995], ![-434, 4766, 0]], ![![-5179, -5179, -4737], ![-2070, 22690, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {5} * I5N1 =  Ideal.span {B.equivFun.symm ![-5874, -1108, -209]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E17RS1 : RelationCertificate Table 5 ![![17, 0, 0], ![-4, 1, 0]]
  ![-4, 1, 0] ![![5, 0, 0], ![1, -1, 1]] where
    su := ![![85, 0, 0], ![-20, 5, 0]]
    hsu := by decide
    w := ![![-20, 5, 0], ![145, 5, -5]]
    hw := by decide
    g := ![![![3, 1, 0], ![1, 0, 0]], ![![0, 1, -1], ![5, 0, 0]]]
    h := ![![![-84, 25, -1], ![-356, 17, 0]], ![![617, -158, 1], ![2615, -18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {5} * I17N1 =  Ideal.span {B.equivFun.symm ![-4, 1, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E23RS1 : RelationCertificate Table 5 ![![23, 0, 0], ![-10, 1, 0]]
  ![-230996887, -43572322, -8218930] ![![5, 0, 0], ![1, -1, 1]] where
    su := ![![115, 0, 0], ![-50, 5, 0]]
    hsu := by decide
    w := ![![-1154984435, -217861610, -41094650], ![-5498652295, -1037196005, -195643495]]
    hw := by decide
    g := ![![![33122, -4265, -1587], ![7161, 0, 0]], ![![-15306, 3259, 540], ![-3602, 0, 0]]]
    h := ![![![-1062835859, 114839115, -1502776], ![-2421422787, 26344918, 0]], ![![-5059951243, 546726274, -7154416], ![-11527914813, 125422869, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {5} * I23N1 =  Ideal.span {B.equivFun.symm ![-230996887, -43572322, -8218930]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 5 ![![29, 0, 0], ![-9, 1, 0]]
  ![17, 18, -4] ![![5, 0, 0], ![1, -1, 1]] where
    su := ![![145, 0, 0], ![-45, 5, 0]]
    hsu := by decide
    w := ![![85, 90, -20], ![3295, -595, -5]]
    hw := by decide
    g := ![![![2136, 483, 11], ![337, 0, 0]], ![![-273, -61, -2], ![-40, 0, 0]]]
    h := ![![![94, -2, -1], ![301, 25, 0]], ![![3520, -411, 2], ![11269, -59, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {5} * I29N1 =  Ideal.span {B.equivFun.symm ![17, 18, -4]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 
