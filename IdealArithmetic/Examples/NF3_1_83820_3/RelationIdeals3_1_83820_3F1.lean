import IdealArithmetic.Examples.NF3_1_83820_3.PrimesBelow3_1_83820_3F1
import IdealArithmetic.Examples.NF3_1_83820_3.ClassGroupData3_1_83820_3

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 3 ![![37, 0, 0], ![-12, 1, 0]]
  ![3572446, -1311687, 299768] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![111, 0, 0], ![-36, 3, 0]]
    hsu := by decide
    w := ![![10717338, -3935061, 899304], ![-31263717, 11479029, -2623374]]
    hw := by decide
    g := ![![![-8569, 536, 810], ![3035, -104, 0]], ![![1234, -167, -156], ![-465, 32, 0]]]
    h := ![![![-1229231, 19446096, -3242986], ![924261, 60145125, 0]], ![![3585837, -56726518, 9460166], ![-2696091, -175450300, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {3} * I37N1 =  Ideal.span {B.equivFun.symm ![3572446, -1311687, 299768]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E37RS1 


noncomputable def E43RS1 : RelationCertificate Table 9 ![![43, 0, 0], ![10, 1, 0]]
  ![-13, 6, -2] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![387, 0, 0], ![90, 9, 0]]
    hsu := by decide
    w := ![![-117, 54, -18], ![234, -81, 18]]
    hw := by decide
    g := ![![![-34, 143, -72], ![31, 327, 0]], ![![2329, -13550, 6916], ![-2531, -31121, 0]]]
    h := ![![![1354, 15164, 3036], ![704, -65275, 0]], ![![-2705, -30070, -6020], ![-1309, 129431, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R43N1 : Ideal.span {9} * I43N1 =  Ideal.span {B.equivFun.symm ![-13, 6, -2]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E43RS1 


noncomputable def E53RS1 : RelationCertificate Table 9 ![![53, 0, 0], ![-8, 1, 0]]
  ![907, -24, -37] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![477, 0, 0], ![-72, 9, 0]]
    hsu := by decide
    w := ![![8163, -216, -333], ![-396, 189, 63]]
    hw := by decide
    g := ![![![-1599, 5728, -2859], ![1357, 12561, 0]], ![![348, -938, 459], ![-250, -1975, 0]]]
    h := ![![![-11859, 99403, -24869], ![3697, 659010, 0]], ![![586, -4888, 1223], ![-163, -32406, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R53N1 : Ideal.span {9} * I53N1 =  Ideal.span {B.equivFun.symm ![907, -24, -37]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E53RS1 


noncomputable def E59RS0 : RelationCertificate Table 9 ![![59, 0, 0], ![0, 1, 0]]
  ![-4865, 66, 182] ![![9, 0, 0], ![-4, 1, 0]] where
    su := ![![531, 0, 0], ![0, 9, 0]]
    hsu := by decide
    w := ![![-43785, 594, 1638], ![3510, -1125, -414]]
    hw := by decide
    g := ![![![42536, -363860, 187828], ![-59330, -855083, 0]], ![![4250, -9426, 4534], ![-2931, -19108, 0]]]
    h := ![![![-83, 2, 2], ![-52, 32, 0]], ![![6, -6, -2], ![229, 36, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N0 : Ideal.span {9} * I59N0 =  Ideal.span {B.equivFun.symm ![-4865, 66, 182]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E59RS0 


noncomputable def E59RS1 : RelationCertificate Table 3 ![![59, 0, 0], ![28, 1, 0]]
  ![48599, -17844, 4078] ![![3, 0, 0], ![-1, 1, 0]] where
    su := ![![177, 0, 0], ![84, 3, 0]]
    hsu := by decide
    w := ![![145797, -53532, 12234], ![-425307, 156159, -35688]]
    hw := by decide
    g := ![![![-1243, -180, 30], ![356, 0, 0]], ![![-633, -100, 12], ![178, 1, 0]]]
    h := ![![![1655313, 73221368, 5232642], ![2026644, -154360900, 0]], ![![-4828791, -213595342, -15264232], ![-5911857, 450288896, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R59N1 : Ideal.span {3} * I59N1 =  Ideal.span {B.equivFun.symm ![48599, -17844, 4078]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E59RS1 
