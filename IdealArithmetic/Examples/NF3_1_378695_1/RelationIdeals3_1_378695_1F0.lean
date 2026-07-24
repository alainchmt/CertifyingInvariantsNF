import IdealArithmetic.Examples.NF3_1_378695_1.PrimesBelow3_1_378695_1F0
import IdealArithmetic.Examples.NF3_1_378695_1.ClassGroupData3_1_378695_1

set_option linter.all false

noncomputable section


noncomputable def E5RS1 : RelationCertificate Table 41 ![![5, 0, 0], ![2, 1, 0]]
  ![-83541, 31408, -3547] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![205, 0, 0], ![82, 41, 0]]
    hsu := by decide
    w := ![![-3425181, 1287728, -145427], ![405572, -152479, 17220]]
    hw := by decide
    g := ![![![56, -106, -35], ![13, 1368, 0]], ![![82, -84, -28], ![17, 1062, 0]]]
    h := ![![![-3743167, -2309975, -227223], ![9316147, 1132568, 0]], ![![443220, 273519, 26905], ![-1103104, -134105, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R5N1 : Ideal.span {41} * I5N1 =  Ideal.span {B.equivFun.symm ![-83541, 31408, -3547]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E5RS1 


noncomputable def E7RS0 : RelationCertificate Table 41 ![![7, 0, 0], ![-34, 3, 1]]
  ![-34, -4, 1] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![287, 0, 0], ![-1394, 123, 41]]
    hsu := by decide
    w := ![![-1394, -164, 41], ![-287, 0, 0]]
    hw := by decide
    g := ![![![-63, 35268, 11763], ![860, -482283, 0]], ![![298, -167739, -55946], ![-4059, 2293785, 0]]]
    h := ![![![0, -1, 0], ![1, 0, 0]], ![![33, -3, -1], ![7, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N0 : Ideal.span {41} * I7N0 =  Ideal.span {B.equivFun.symm ![-34, -4, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS0 


noncomputable def E7RS1 : RelationCertificate Table 41 ![![7, 0, 0], ![3, 1, 0]]
  ![7, -4, 1] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![287, 0, 0], ![123, 41, 0]]
    hsu := by decide
    w := ![![287, -164, 41], ![-164, 41, 0]]
    hw := by decide
    g := ![![![1, -168, -56], ![0, 2295, 0]], ![![1, -87, -29], ![1, 1188, 0]]]
    h := ![![![370, 164, 14], ![-861, -97, 0]], ![![-232, -104, -9], ![540, 63, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R7N1 : Ideal.span {41} * I7N1 =  Ideal.span {B.equivFun.symm ![7, -4, 1]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E7RS1 


noncomputable def E13RS0 : RelationCertificate Table 41 ![![13, 0, 0], ![-27, 2, 1]]
  ![-100051, 37615, -4248] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![533, 0, 0], ![-1107, 82, 41]]
    hsu := by decide
    w := ![![-4102091, 1542215, -174168], ![485727, -182614, 20623]]
    hw := by decide
    g := ![![![-26, -292, -97], ![-4, 3996, 0]], ![![27, 600, 201], ![50, -8289, 0]]]
    h := ![![![-1318, 2421, -563], ![3071, 0, 0]], ![![174, -288, 66], ![-355, 0, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N0 : Ideal.span {41} * I13N0 =  Ideal.span {B.equivFun.symm ![-100051, 37615, -4248]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS0 


noncomputable def E13RS1 : RelationCertificate Table 41 ![![13, 0, 0], ![-3, 1, 0]]
  ![357, 124, 10] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![533, 0, 0], ![-123, 41, 0]]
    hsu := by decide
    w := ![![14637, 5084, 410], ![-779, 1189, 164]]
    hw := by decide
    g := ![![![1164, -722243, -240910], ![-17525, 9877104, 0]], ![![-157, 143781, 47972], ![3496, -1966680, 0]]]
    h := ![![![48948, -17027, 244], ![211989, -3162, 0]], ![![-2746, 957, -13], ![-11893, 173, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R13N1 : Ideal.span {41} * I13N1 =  Ideal.span {B.equivFun.symm ![357, 124, 10]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E13RS1 


noncomputable def E17RS1 : RelationCertificate Table 41 ![![17, 0, 0], ![4, 1, 0]]
  ![12868, -1865, -446] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![697, 0, 0], ![164, 41, 0]]
    hsu := by decide
    w := ![![527588, -76465, -18286], ![121114, -13243, -3649]]
    hw := by decide
    g := ![![![-14246, 965709, 319973], ![22550, -13140820, 0]], ![![2396, 249605, 83732], ![6289, -3428040, 0]]]
    h := ![![![1377836, 371593, 6832], ![-5852586, -116590, 0]], ![![316746, 85421, 1569], ![-1345432, -26762, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R17N1 : Ideal.span {41} * I17N1 =  Ideal.span {B.equivFun.symm ![12868, -1865, -446]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E17RS1 


noncomputable def E23RS0 : RelationCertificate Table 41 ![![23, 0, 0], ![7, 1, 0]]
  ![-6937, 28, 116] ![![41, 0, 0], ![3, 1, 0]] where
    su := ![![943, 0, 0], ![287, 41, 0]]
    hsu := by decide
    w := ![![-284417, 1148, 4756], ![-42271, -1517, 492]]
    hw := by decide
    g := ![![![6412, -2123613, -707842], ![-51297, 29026150, 0]], ![![1075, -661335, -220592], ![-16042, 9044100, 0]]]
    h := ![![![-16261, -2538, -32], ![52438, 852, 0]], ![![-2423, -380, -5], ![7814, 127, 0]]]
    hle1 := by decide
    hle2 := by decide

lemma R23N0 : Ideal.span {41} * I23N0 =  Ideal.span {B.equivFun.symm ![-6937, 28, 116]} * (J0 ^ 1) := by
  exact relation_of_RelationCertificate timesTableT_eq_Table rfl PowJ0_1 E23RS0 
