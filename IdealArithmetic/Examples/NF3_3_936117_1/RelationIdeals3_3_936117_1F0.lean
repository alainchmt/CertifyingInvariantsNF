import IdealArithmetic.Examples.NF3_3_936117_1.PrimesBelow3_3_936117_1F0
import IdealArithmetic.Examples.NF3_3_936117_1.ClassGroupData3_3_936117_1

set_option linter.all false

noncomputable section


noncomputable def E2RS0 : RelationCertificate Table 4 ![![2, 0, 0], ![-43, -1, 1]]
  ![-95, -79, -9] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![8, 0, 0], ![-172, -4, 4]]
    hsu := by decide
    w := ![![-380, -316, -36], ![-896, -768, -88]]
    hw := by decide
    g := ![![![13, 0, -9], ![6, 31, 0]], ![![133, 225, 151], ![90, -651, 0]]]
    h := ![![![17, -38, -6], ![3, 0, 0]], ![![17, -93, -14], ![6, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N0 : Ideal.span {4} * I2N0 =  Ideal.span {B.equivFun.symm ![-95, -79, -9]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E2RS0 


noncomputable def E2RS1 : RelationCertificate Table 1 ![![2, 0, 0], ![1, 1, 0]]
  ![1, 0, 0] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![2, 0, 0], ![1, 1, 0]]
    hsu := by decide
    w := ![![2, 0, 0], ![1, 1, 0]]
    hw := by decide
    g := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    h := ![![![0, -1, 0], ![2, 0, 0]], ![![0, 0, 0], ![1, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R2N1 : Ideal.span {1} * I2N1 =  Ideal.span {B.equivFun.symm ![1, 0, 0]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E2RS1 


noncomputable def E5RS0 : RelationCertificate Table 2 ![![5, 0, 0], ![-42, -2, 1]]
  ![-71, -61, -7] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![10, 0, 0], ![-84, -4, 2]]
    hsu := by decide
    w := ![![-142, -122, -14], ![-694, -594, -68]]
    hw := by decide
    g := ![![![22, -11, -10], ![6, 19, 0]], ![![-151, 92, 78], ![-29, -152, 0]]]
    h := ![![![11, -11, -2], ![3, 0, 0]], ![![23, -55, -9], ![11, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N0 : Ideal.span {2} * I5N0 =  Ideal.span {B.equivFun.symm ![-71, -61, -7]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS0 


noncomputable def E5RS1 : RelationCertificate Table 4 ![![5, 0, 0], ![2, 1, 0]]
  ![61, 1, -1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![20, 0, 0], ![8, 4, 0]]
    hsu := by decide
    w := ![![244, 4, -4], ![-28, -4, 0]]
    hw := by decide
    g := ![![![2, 5, 4], ![4, -17, 0]], ![![-4, -1, 2], ![3, -7, 0]]]
    h := ![![![273, 159, 14], ![-652, -71, 0]], ![![-35, -21, -2], ![84, 10, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {4} * I5N1 =  Ideal.span {B.equivFun.symm ![61, 1, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 2 ![![7, 0, 0], ![2, 1, 0]]
  ![153, 131, 15] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![14, 0, 0], ![4, 2, 0]]
    hsu := by decide
    w := ![![306, 262, 30], ![1488, 1274, 146]]
    hw := by decide
    g := ![![![-248, 175, 166], ![-35, -324, 0]], ![![-32, 59, 68], ![14, -135, 0]]]
    h := ![![![385, 216, 10], ![-1271, -55, 0]], ![![1876, 1055, 50], ![-6194, -277, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {2} * I7N0 =  Ideal.span {B.equivFun.symm ![153, 131, 15]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 2 ![![7, 0, 0], ![-1, 1, 0]]
  ![15, 7, -1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![14, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![30, 14, -2], ![-74, -44, 6]]
    hw := by decide
    g := ![![![-31, 143, 175], ![57, -351, 0]], ![![-2, -14, -14], ![-8, 27, 0]]]
    h := ![![![6, -2, -1], ![27, 6, 0]], ![![-10, 2, 0], ![-33, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {2} * I7N1 =  Ideal.span {B.equivFun.symm ![15, 7, -1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E11RS0 : RelationCertificate Table 4 ![![11, 0, 0], ![-43, 1, 1]]
  ![-63, -19, 3] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![44, 0, 0], ![-172, 4, 4]]
    hsu := by decide
    w := ![![-252, -76, 12], ![204, 116, -16]]
    hw := by decide
    g := ![![![5991, -101910, -107902], ![-23976, 431607, 0]], ![![-23986, 407621, 431606], ![95910, -1726428, 0]]]
    h := ![![![6, -2, 0], ![3, 0, 0]], ![![32, 2, -1], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N0 : Ideal.span {4} * I11N0 =  Ideal.span {B.equivFun.symm ![-63, -19, 3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E11RS0 


noncomputable def E11RS1 : RelationCertificate Table 2 ![![11, 0, 0], ![-1, 1, 0]]
  ![5, 5, 1] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![22, 0, 0], ![-2, 2, 0]]
    hsu := by decide
    w := ![![10, 10, 2], ![94, 76, 6]]
    hw := by decide
    g := ![![![-687, 485, 463], ![-99, -903, 0]], ![![136, -42, -24], ![48, 43, 0]]]
    h := ![![![2, -1, 0], ![17, 1, 0]], ![![10, -2, 0], ![63, 3, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R11N1 : Ideal.span {2} * I11N1 =  Ideal.span {B.equivFun.symm ![5, 5, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E11RS1 


noncomputable def E13RS0 : RelationCertificate Table 4 ![![13, 0, 0], ![6, 1, 0]]
  ![-29, -25, -3] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![52, 0, 0], ![24, 4, 0]]
    hsu := by decide
    w := ![![-116, -100, -12], ![-296, -252, -28]]
    hw := by decide
    g := ![![![-213, 2, -2], ![-49, 22, 0]], ![![-76, -1, -2], ![-16, 13, 0]]]
    h := ![![![-281, -71, -4], ![604, 49, 0]], ![![-710, -173, -9], ![1526, 110, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {4} * I13N0 =  Ideal.span {B.equivFun.symm ![-29, -25, -3]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 4 ![![13, 0, 0], ![-3, 1, 0]]
  ![757, 341, -49] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![52, 0, 0], ![-12, 4, 0]]
    hsu := by decide
    w := ![![3028, 1364, -196], ![-3604, -2136, 292]]
    hw := by decide
    g := ![![![-2977, -1320, 872], ![-1071, -4761, 0]], ![![-1269, -1322, -399], ![-644, 1035, 0]]]
    h := ![![![9439, -3241, 43], ![40650, -608, 0]], ![![-11179, 3832, -51], ![-48142, 736, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {4} * I13N1 =  Ideal.span {B.equivFun.symm ![757, 341, -49]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E13RS1 


noncomputable def E23RS1 : RelationCertificate Table 4 ![![23, 0, 0], ![-9, 1, 0]]
  ![-27, -11, -1] ![![4, 0, 0], ![1, 1, 0]] where
    su := ![![92, 0, 0], ![-36, 4, 0]]
    hsu := by decide
    w := ![![-108, -44, -4], ![-116, -104, -12]]
    hw := by decide
    g := ![![![359, -5795, -6149], ![-1357, 24589, 0]], ![![-141, 2158, 2295], ![506, -9175, 0]]]
    h := ![![![-1044, 133, -2], ![-2665, 45, 0]], ![![-1102, 138, -2], ![-2813, 43, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N1 : Ideal.span {4} * I23N1 =  Ideal.span {B.equivFun.symm ![-27, -11, -1]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E23RS1 


noncomputable def E29RS1 : RelationCertificate Table 2 ![![29, 0, 0], ![5, 1, 0]]
  ![-319, -271, -31] ![![2, 0, 0], ![1, 1, 0]] where
    su := ![![58, 0, 0], ![10, 2, 0]]
    hsu := by decide
    w := ![![-638, -542, -62], ![-3078, -2636, -302]]
    hw := by decide
    g := ![![![200, -2570, -2901], ![-1185, 5865, 0]], ![![107, -421, -520], ![-156, 1035, 0]]]
    h := ![![![-321, -76, -2], ![1798, 27, 0]], ![![-1551, -354, -7], ![8688, 52, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R29N1 : Ideal.span {2} * I29N1 =  Ideal.span {B.equivFun.symm ![-319, -271, -31]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E29RS1 
