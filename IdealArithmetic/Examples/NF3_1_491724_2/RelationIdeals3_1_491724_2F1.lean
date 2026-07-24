import IdealArithmetic.Examples.NF3_1_491724_2.PrimesBelow3_1_491724_2F1
import IdealArithmetic.Examples.NF3_1_491724_2.ClassGroupData3_1_491724_2

set_option linter.all false

noncomputable section


noncomputable def E37RS1 : RelationCertificate Table 49 ![![37, 0, 0], ![-11, 1, 0]]
  ![-42851, -3160, 424] ![![49, 0, 0], ![13, 1, 0]] where
    su := ![![1813, 0, 0], ![-539, 49, 0]]
    hsu := by decide
    w := ![![-2099699, -154840, 20776], ![-233975, -17787, 2352]]
    hw := by decide
    g := ![![![-4227888, 836263191, 64352964], ![15944941, -3153293004, 0]], ![![1276861, -252385477, -19421822], ![-4811940, 951669486, 0]]]
    h := ![![![-26334436, 2563320, -15395], ![-88575571, 570039, 0]], ![![-2934418, 285634, -1716], ![-9869881, 63540, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R37N1 : Ideal.span {49} * I37N1 =  Ideal.span {B.equivFun.symm ![-42851, -3160, 424]} * (J0 ^ 2) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_2 E37RS1 


noncomputable def E41RS1 : RelationCertificate Table 7 ![![41, 0, 0], ![-2, 1, 0]]
  ![673, 69, -8] ![![7, 0, 0], ![-1, 1, 0]] where
    su := ![![287, 0, 0], ![-14, 7, 0]]
    hsu := by decide
    w := ![![4711, 483, -56], ![-6769, -644, 77]]
    hw := by decide
    g := ![![![-172, -76, 23], ![15, -184, 0]], ![![-51, -16, -1], ![11, 0, 0]]]
    h := ![![![9199, -4600, 5], ![188243, -213, 0]], ![![-13209, 6607, -8], ![-270301, 339, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R41N1 : Ideal.span {7} * I41N1 =  Ideal.span {B.equivFun.symm ![673, 69, -8]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E41RS1 
