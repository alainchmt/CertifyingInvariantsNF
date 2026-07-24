import IdealArithmetic.Examples.NF3_1_30251_1.PrimesBelow3_1_30251_1F0
import IdealArithmetic.Examples.NF3_1_30251_1.ClassGroupData3_1_30251_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 4 ![![2, 0, 0], ![1, 1, 1]]
  ![-45, 7, 1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![8, 0, 0], ![4, 4, 4]]
    hsu := by decide
    w := ![![-180, 28, 4], ![-56, -48, 40]]
    hw := by decide
    g := ![![![52, -2, 49], ![27, -31, 0]], ![![369, -13, 111], ![186, -31, 0]]]
    h := ![![![-20, 6, 3], ![-5, 0, 0]], ![![-6, -5, 6], ![-2, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {4} * I2N0 =  Ideal.span {B.equivFun.symm ![-45, 7, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![0, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![2, 0, 0], ![0, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![0, 1, 0]]
    hw := by decide
    g := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![1, 0, 0], ![0, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![-1, 1, 1]]
  ![9, -9, 5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![14, 0, 0], ![-2, 2, 2]]
    hsu := by decide
    w := ![![18, -18, 10], ![170, 12, -30]]
    hw := by decide
    g := ![![![48, 283, -870], ![143, 351, 0]], ![![83, -39, 148], ![-18, -54, 0]]]
    h := ![![![2, -2, 0], ![5, 0, 0]], ![![12, 1, -2], ![-1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![9, -9, 5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 4 ![![7, 0, 0], ![-1, 1, 0]]
  ![-1, -1, 1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![28, 0, 0], ![-4, 4, 0]]
    hsu := by decide
    w := ![![-4, -4, 4], ![32, -4, 0]]
    hw := by decide
    g := ![![![1, 0, 4], ![1, -3, 0]], ![![-1, -1, 4], ![4, -3, 0]]]
    h := ![![![-2, 3, -2], ![-13, 3, 0]], ![![24, -23, 0], ![160, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {4} * I7N1 =  Ideal.span {B.equivFun.symm ![-1, -1, 1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E7RS1 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![4, 1, 0]]
  ![-13, 1, 1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![22, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![-26, 2, 2], ![34, -18, 8]]
    hw := by decide
    g := ![![![41, -24, 89], ![-12, -33, 0]], ![![35, -6, 28], ![-1, -9, 0]]]
    h := ![![![-11, -4, -4], ![27, 9, 0]], ![![7, 0, -1], ![-15, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![-13, 1, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 2 ![![13, 0, 0], ![4, 1, 0]]
  ![3, 1, -1] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![26, 0, 0], ![8, 2, 0]]
    hsu := by decide
    w := ![![6, 2, -2], ![-34, 4, 2]]
    hw := by decide
    g := ![![![10, 41, -126], ![21, 51, 0]], ![![7, 82, -254], ![41, 102, 0]]]
    h := ![![![11, 2, -2], ![-35, 5, 0]], ![![-105, -27, -3], ![337, 8, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {2} * I13N0 =  Ideal.span {B.equivFun.symm ![3, 1, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E17RS0 : RelationCertificate Table 4 ![![17, 0, 0], ![0, 1, 0]]
  ![-17, -1, -3] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![68, 0, 0], ![0, 4, 0]]
    hsu := by decide
    w := ![![-68, -4, -12], ![-136, -8, -20]]
    hw := by decide
    g := ![![![-5, 0, -1], ![-1, 0, 1]], ![![10, 0, 1], ![-2, 0, -1]]]
    h := ![![![-1, -3, 6], ![8, -21, 0]], ![![-2, -5, 10], ![13, -35, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N0 : Ideal.span {4} * I17N0 =  Ideal.span {B.equivFun.symm ![-17, -1, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS0 


noncomputable def E17RS1 : RelationCertificate Table 4 ![![17, 0, 0], ![6, 1, 0]]
  ![69, 5, 11] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![68, 0, 0], ![24, 4, 0]]
    hsu := by decide
    w := ![![276, 20, 44], ![512, 36, 80]]
    hw := by decide
    g := ![![![-7, 2, 54], ![-3, -43, 0]], ![![-2, 0, 23], ![-1, -18, 0]]]
    h := ![![![-45, -10, -2], ![139, 9, 0]], ![![-68, -13, 0], ![214, 4, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {4} * I17N1 =  Ideal.span {B.equivFun.symm ![69, 5, 11]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS1 


noncomputable def E17RS2 : RelationCertificate Table 4 ![![17, 0, 0], ![-7, 1, 0]]
  ![-19, 5, -1] ![![4, 0, 0], ![2, 1, 0]] where
    su := ![![68, 0, 0], ![-28, 4, 0]]
    hsu := by decide
    w := ![![-76, 20, -4], ![-72, -16, 20]]
    hw := by decide
    g := ![![![-29, 0, 2915131], ![-10, -2332109, 0]], ![![1, -1, -1371332], ![5, 1097066, 0]]]
    h := ![![![-46, 12, -3], ![-109, 10, 0]], ![![-34, 14, -5], ![-80, 18, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N2 : Ideal.span {4} * I17N2 =  Ideal.span {B.equivFun.symm ![-19, 5, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E17RS2 


noncomputable def E23RS1 : RelationCertificate Table 2 ![![23, 0, 0], ![-1, 1, 0]]
  ![23, 3, -5] ![![2, 0, 0], ![0, 1, 0]] where
    su := ![![46, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![46, 6, -10], ![-170, 32, 0]]
    hw := by decide
    g := ![![![256, 451, -1325], ![227, 546, 0]], ![![48, 75, -220], ![39, 91, 0]]]
    h := ![![![4, 0, -5], ![69, 22, 0]], ![![-14, 14, -5], ![-237, 23, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {2} * I23N1 =  Ideal.span {B.equivFun.symm ![23, 3, -5]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS1 
